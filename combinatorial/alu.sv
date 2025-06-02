// Buggy ALU Design

module buggy_alu (
    input  logic [7:0] a, b,     // 8-bit operands
    input  logic [2:0] op,       // Operation select
    output logic [7:0] result,   // Result
    output logic       zero,     // Zero flag
    output logic       overflow, // Overflow flag
    output logic       carry     // Carry flag
);

    // Operation codes
    localparam ADD = 3'b000;
    localparam SUB = 3'b001;
    localparam AND = 3'b010;
    localparam OR  = 3'b011;
    localparam XOR = 3'b100;
    localparam SHL = 3'b101;
    localparam SHR = 3'b110;
    // BUG: Missing operation code for NOT (3'b111)

    logic [8:0] temp_result; // For carry calculation

    always_comb begin
        // Default assignments
        result = 8'b0;
        zero = 1'b0;
        overflow = 1'b0;
        carry = 1'b0;
        temp_result = 9'b0;

        case (op)
            ADD: begin
                // BUG: Incorrect carry calculation
                temp_result = a + b;
                result = temp_result[7:0];
                carry = temp_result[7]; // BUG: Should be temp_result[8]
                overflow = (a[7] == b[7]) && (result[7] != a[7]);
            end

            SUB: begin
                // BUG: Operands in wrong order
                temp_result = b - a; // Should be a - b
                result = temp_result[7:0];
                carry = temp_result[8];
                overflow = (a[7] != b[7]) && (result[7] == b[7]);
            end

            AND: begin
                result = a & b;
            end

            OR: begin
                result = a | b;
            end

            XOR: begin
                result = a ^ b;
            end

            SHL: begin
                // BUG: Incorrect shift implementation
                result = a << 1; // Should use b as shift amount
                carry = a[7];
            end

            SHR: begin
                result = a >> b[2:0];
                carry = (b[2:0] > 0) ? a[b[2:0]-1] : 1'b0;
            end

            // BUG: Missing default case
        endcase

        // BUG: Incorrect zero flag implementation
        zero = ~|result; // This is actually correct, but students should verify why
    end

    // Assertion to catch timing violations
    property valid_op_check;
        @(posedge carry) op inside {ADD, SUB, SHL, SHR};
    endproperty
    assert property (valid_op_check) else $error("Invalid operation for carry flag");

endmodule 