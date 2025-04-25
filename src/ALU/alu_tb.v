`include "alu.v"
`default_nettype none

module tb_alu;
logic clk;
logic [1:0] opcode;
logic [7:0] a;
logic [7:0] b;
logic [7:0] result;

alu  DUT(
    .opcode(opcode),
    .a(a),
    .b(b),
    .result(result)
);

localparam CLK_PERIOD = 10;
always #(CLK_PERIOD/2) clk=~clk;

initial begin
    $dumpfile("tb_alu.vcd");
    $dumpvars(0, tb_alu);
end

initial begin
    #1 clk<=1'b0;
    a = 1;
    b = 1;
    opcode = 2'b00;
    repeat (5)@(posedge clk);
    assert (result == 2)
      $info("ADD Assertion passed: result is equal to 2");
    else
      $error("ADD Assertion failed: result is not equal to 2");
    opcode = 2'b01;
    repeat (5)@(posedge clk);
    assert (result == 0)
      $info("SUB Assertion passed: result is equal to 0");
    else
      $error("SUB Assertion failed: result is not equal to 0");
      opcode = 2'b10;
      repeat (5)@(posedge clk);
      assert (result == 1)
        $info("AND Assertion passed: result is equal to 1");
      else
        $error("AND Assertion failed: result is not equal to 1");
        opcode = 2'b11;
    repeat (5)@(posedge clk);
    assert (result == 1)
      $info("OR Assertion passed: result is equal to 1");
    else
      $error("OR Assertion failed: result is not equal to 1");
    @(posedge clk);
    repeat(2) @(posedge clk);
    $finish;
end

endmodule
