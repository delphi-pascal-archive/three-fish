
(**
 * An implementation of Threefish encryption algorithm.
 *
 * Threefish is tweakable block encryption algorithm designed by Bruce Schneier,
 * Niels Ferguson, Stefan Lucks, Doug Whiting, Mihir Bellare, Tadayoshi Kohno,
 * Jon Callas, and Jesse Walker.
 *
 *
 * Delphi implementation by Alexander Myasnikov
 *
 * Web: www.darksoftware.narod.ru
 *)

library libthreefish512;

const
  blockSize = 64;
const
  Nw = 8;
const
  Nr = 72;

const
  constant: uint64 = 6148914691236517205;

const
  p: array [0..7] of longword = (2, 1, 4, 7, 6, 5, 0, 3);
const
  p_1: array [0..7] of longword = (6, 1, 0, 7, 2, 5, 4, 3);

const
  r: array[0..7, 0..3] of longword =
    ((38, 30, 50, 53), (48, 20, 43, 31), (34, 14, 15, 27), (26, 12, 58, 7),
    (33, 49, 8, 42), (39, 27, 41, 14), (29, 26, 11, 9), (33, 51, 39, 35));

var
  t: array[0..2] of uint64;
var
  subKeys: array [0..18, 0..7] of uint64;


type
  t2_64 = array [0..1] of uint64;
type
  p2_64 = ^t2_64;


  procedure _mix (x: p2_64; r: longword; y: p2_64);
  begin
    y[0] := x[0] + x[1];
    y[1] := (x[1] shl r) or (x[1] shr (64 - r));
    y[1] := y[1] xor y[0];
  end;


  procedure _demix (y: p2_64; r: longword; x: p2_64);
  begin
    y[1] := y[1] xor y[0];
    x[1] := (y[1] shl (64 - (r))) or (y[1] shr (r));
    x[0] := y[0] - x[1];
  end;


type
  t8_64 = array [0..7] of uint64;
type
  p8_64 = ^t8_64;


  procedure crypt (plain, c: p8_64); stdcall; export;
  var
    round, s, i: longword;
    f, e, v: t8_64;
    y, x: t2_64;
  begin

    move(plain^, v, 64);


    for round := 0 to Nr - 1 do
      begin

      if (round mod 4 = 0) then
        begin
        s := round div 4;
        for i := 0 to Nw - 1 do
          begin
          e[i] := v[i] + subKeys[s][i];
          end;
        end
      else
        begin
        for i := 0 to nw - 1 do
          begin
          e[i] := v[i];
          end;
        end;


      for i := 0 to (Nw div 2) - 1 do
        begin

        x[0] := e[i * 2];
        x[1] := e[i * 2 + 1];

        _mix(@x, r[round mod 8][i], @y);

        f[i * 2] := y[0];
        f[i * 2 + 1] := y[1];
        end;

      for i := 0 to nw - 1 do
        begin
        v[i] := f[p[i]];
        end;

      end;

    for i := 0 to nw - 1 do
      begin
      c[i] := v[i] + subKeys[Nr div 4][i];
      end;

  end;


  procedure decrypt (plain, c: p8_64); stdcall; export;
  var
    round, s, i: longword;
    f, e, v: t8_64;
    y, x: t2_64;

  begin

    move(plain^, v, 64);

    for round := Nr downto 1 do
      begin

      if (round mod 4 = 0) then
        begin
        s := round div 4;
        for i := 0 to nw - 1 do
          begin
          f[i] := v[i] - subKeys[s][i];
          end;
        end
      else
        begin
        for i := 0 to nw - 1 do
          begin
          f[i] := v[i];
          end;
        end;


      for i := 0 to nw - 1 do
        begin
        e[i] := f[p_1[i]];
        end;

      for i := 0 to (Nw div 2) - 1 do
        begin

        y[0] := e[i * 2];
        y[1] := e[i * 2 + 1];

        _demix(@y, r[(round - 1) mod 8][i], @x);

        v[i * 2] := x[0];
        v[i * 2 + 1] := x[1];
        end;

      end;

    for i := 0 to nw - 1 do
      begin
      c[i] := v[i] - subKeys[0][i];
      end;

  end;


  procedure setup (keydata: p8_64; tweakdata: p2_64); stdcall; export;
  var
    i, round: longword;
    K: t8_64;
    key: array [0..8] of uint64;
  var
    kNw: uint64;
  begin
    kNw := constant;


    move(keydata^, K, 64);

    for i := 0 to nw - 1 do
      begin
      kNw := kNw xor K[i];
      key[i] := K[i];
      end;

    key[8] := kNw;

    t[0] := tweakdata^[0];
    t[1] := tweakdata^[1];
    t[2] := tweakdata^[0] xor tweakdata^[1];


    for round := 0 to (Nr div 4) do
      begin
      for i := 0 to nw - 1 do
        begin
        subKeys[round][i] := key[(round + i) mod (Nw + 1)];

        if (i = Nw - 3) then
          begin
          subKeys[round][i] := subKeys[round][i] + t[round mod 3];
          end
        else
          if (i = Nw - 2) then
            begin
            subKeys[round][i] := subKeys[round][i] + t[(round + 1) mod 3];
            end
          else
            if (i = Nw - 1) then
              begin
              subKeys[round][i] := subKeys[round][i] + round;
              end;
        end;
      end;

  end;

exports

  crypt,
  decrypt,
  setup;

end.
