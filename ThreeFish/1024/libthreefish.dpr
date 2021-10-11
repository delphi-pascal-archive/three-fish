library libthreefish;


  (* Threefish-1024 LITE-port from Java implementation of Skein by Maarten Bodewes *)
  (*                        Alexander Myasnikov                                    *)
  (*                 WEB:  www.darksoftware.narod.ru                               *)


const
  EXTENDED_KEY_SCHEDULE_CONST: uint64 = 6148914691236517205;


const
  SUBKEY_INTERVAL: integer = 4;


  //  Word permutation constants for PI(i)

  PI16: array [0..15] of integer =
    (0, 9, 2, 13, 6, 11, 4, 15, 10, 7, 12, 3, 14, 5, 8, 1);


  //  Reverse word permutation constants for PI(i)


const
  RPI16: array [0..15] of integer =
    (0, 15, 2, 11, 6, 13, 4, 9, 14, 1, 8, 5, 10, 3, 12, 7);


const
  DEPTH_OF_D_IN_R: integer = 8;


  // Rotation constants

const
  R16: array [0..7, 0..7] of integer =
    (
    (55, 43, 37, 40, 16, 22, 38, 12),
    (25, 25, 46, 13, 14, 13, 52, 57),
    (33, 8, 18, 57, 21, 12, 32, 54),
    (34, 43, 25, 60, 44, 9, 59, 34),
    (28, 7, 47, 48, 51, 9, 35, 41),
    (17, 6, 18, 25, 43, 42, 40, 15),
    (58, 7, 32, 45, 19, 18, 2, 56),
    (47, 49, 27, 58, 37, 48, 53, 56));


type
  TKey = array [0..16] of uint64;
type
  TTweak = array[0..2] of uint64;

type
  PKey = ^ TKey;
type
  PTweak = ^ TTweak;
var
  t: TTweak;

  x: array [0..1] of uint64;
  y: array [0..1] of uint64;

const
  nr: integer = 80;
var
  k: TKey;
const
  nw: integer = 16;
var
  vd:  array [0..15] of uint64;
var
  ed:  array [0..15] of uint64;
var
  fd:  array [0..15] of uint64;
var
  ksd: array [0..15] of uint64;


  // param j the index in the rotation constants
  // param d the round

  procedure mix (j, d: integer);
  var
    rotl: uint64;
  begin

    y[0] := x[0] + x[1];
    rotl := R16[d mod DEPTH_OF_D_IN_R][j];
    y[1] := ((x[1] shl (rotl)) or (x[1] shr (64 - rotl)));
    y[1] := y[1] xor y[0];
  end;

  procedure demix (j, d: integer);
  var
    rotr: uint64;
  begin

    y[1] := y[1] xor y[0];
    rotr := R16[d mod DEPTH_OF_D_IN_R][j];
    x[1] := (y[1] shr rotr) or (y[1] shl (64 - rotr));
    x[0] := y[0] - x[1];
  end;

  procedure keySchedule (s: integer);
  var
    i: integer;
  begin

    for i := 0 to nw - 1 do
      begin

      ksd[i] := k[(s + i) mod (nw + 1)];

      if (i = nw - 3) then
        begin
        ksd[i] := ksd[i] + t[s mod 3];
        end
      else
      if (i = nw - 2) then
        begin
        ksd[i] := ksd[i] + t[(s + 1) mod 3];
        end
      else
      if (i = nw - 1) then
        begin
        ksd[i] := ksd[i] + s;
        end;
      end;
  end;

  procedure init (key: Pkey; tweak: ptweak);
  var
    i: integer;
    knw: uint64;
  begin

    fillchar(vd, 128, 0);
    fillchar(ed, 128, 0);
    fillchar(fd, 128, 0);
    fillchar(ksd, 128, 0);

    for i := 0 to nw - 1 do
      k[i] := key^[i];


    knw := EXTENDED_KEY_SCHEDULE_CONST;

    for i := 0 to nw - 1 do
      knw := knw xor key^[i];


    k[nw] := knw;


    // set tweak values
    t[0] := tweak^[0];
    t[1] := tweak^[1];
    t[2] := t[0] xor t[1];
  end;

  procedure crypt (p, c: PKey); stdcall; export;
  var
    i, d, j, s: integer;
  begin

    for i := 0 to nw - 1 do
      vd[i] := p^[i];

    for d := 0 to nr - 1 do
      begin
      // calculate e{d,i}
      if (d mod SUBKEY_INTERVAL = 0) then
        begin
        s := d div SUBKEY_INTERVAL;

        keySchedule(s);


        for i := 0 to nw - 1 do
          begin
          ed[i] := vd[i] + ksd[i];
          end;
        end
      else
        begin
        for i := 0 to nw - 1 do
          begin
          ed[i] := vd[i];
          end;
        end;

      for j := 0 to (nw div 2) - 1 do
        begin
        x[0] := ed[j * 2];
        x[1] := ed[j * 2 + 1];

        mix(j, d);

        fd[j * 2] := y[0];
        fd[j * 2 + 1] := y[1];
        end;


      for i := 0 to nw - 1 do
        begin
        vd[i] := fd[PI16[i]];
        end;
      end;

    // do the last keyschedule
    keySchedule(nr div SUBKEY_INTERVAL);


    for i := 0 to nw - 1 do
      begin
      c^[i] := vd[i] + ksd[i];
      end;
  end;

  procedure decrypt (c, p: PKey); stdcall; export;
  var
    i, d, j, s: integer;
  begin

    // initial value = plain
    for i := 0 to nw - 1 do
      vd[i] := c^[i];


    for d := nr downto 1 do
      begin
      // calculate e{d,i}
      if (d mod SUBKEY_INTERVAL = 0) then
        begin
        s := d div SUBKEY_INTERVAL;
        keySchedule(s);

        for i := 0 to nw - 1 do
          begin
          fd[i] := vd[i] - ksd[i];
          end;
        end
      else
        begin
        for i := 0 to nw - 1 do
          begin
          fd[i] := vd[i];
          end;
        end;


      for i := 0 to nw - 1 do
        begin
        ed[i] := fd[RPI16[i]];
        end;


      for j := 0 to (nw div 2) - 1 do
        begin
        y[0] := ed[j * 2];
        y[1] := ed[j * 2 + 1];

        demix(j, d - 1);

        vd[j * 2] := x[0];
        vd[j * 2 + 1] := x[1];
        end;
      end;

    // do the first keyschedule
    keySchedule(0);


    for i := 0 to nw - 1 do
      begin
      p^[i] := vd[i] - ksd[i];
      end;
  end;

  procedure setup (key: PKey; tweak: PTweak); stdcall; export;
  begin
    init(key, tweak);
  end;


exports
  crypt,
  decrypt,
  setup;

end.
