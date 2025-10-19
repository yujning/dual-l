// 文件名：dual_lut_example.v
module dual_lut_example (
    input  wire A,
    input  wire B,
    input  wire C,
    input  wire D,
    input  wire E,
    input  wire F,
    output wire O1,
    output wire O2
);

    // 逻辑实现
    assign O1 = A & B & D & E;
    assign O2 = (A & B & C & F) | (A & B & D & E);

endmodule
