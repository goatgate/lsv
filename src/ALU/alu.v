module alu (
    input logic [1:0] opcode,
    input logic [7:0] a,
    input logic [7:0] b,
    output logic [7:0] result
);
    always_comb
    begin
        case (opcode)
        2'b00: result = a + b;  // ADD
        2'b01: result = a - b;  // SUB
        2'b10: result = a & b;  // AND
        2'b11: result = a | b;  // OR
        default: result = 8'bx;
        endcase
    end
endmodule