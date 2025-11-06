module mux_4_1 (
    input  wire a,
    input  wire b,
    input  wire c,
    input  wire d,
    input  wire s0,
    input  wire s1,
    output wire y
);

  wire tmp0;
  wire tmp1;
  mux_2_1 mux_0 (
      .a (a),
      .b (b),
      .s0(s0),
      .y (tmp0)
  );

  mux_2_1 mux_1 (
      .a (c),
      .b (d),
      .s0(s0),
      .y (tmp1)
  );

  mux_2_1 mux_2 (
      .a (tmp0),
      .b (tmp1),
      .s0(s1),
      .y (y)
  );

endmodule
