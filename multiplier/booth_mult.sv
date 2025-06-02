// Buggy Booth Multiplier


module booth_multiplier #(
    parameter WIDTH = 8
)(
    input  logic                 clk,
    input  logic                 rst_n,
    input  logic                 start,         // Start multiplication
    input  logic [WIDTH-1:0]     multiplicand,  // First operand
    input  logic [WIDTH-1:0]     multiplier,    // Second operand
    output logic [2*WIDTH-1:0]   product,       // Final product
    output logic                 done           // Multiplication complete
);

    // Internal registers
    logic [WIDTH-1:0]   mcand_reg;       // Registered multiplicand
    logic [WIDTH:0]     mplier_reg;      // Registered multiplier with extra bit
    logic [2*WIDTH:0]   partial_product; // Partial product with extra bit
    logic [3:0]         bit_counter;     // Iteration counter
    logic               processing;       // Multiplication in progress

    // Booth encoding signals
    logic [1:0]         booth_encoding;
    logic [WIDTH-1:0]   booth_multiple;

    // BUG: Incorrect state handling
    always_ff @(posedge clk) begin
        if (!rst_n) begin
            processing <= 1'b0;
            bit_counter <= '0;
            done <= 1'b0;
        end else begin
            if (start && !processing) begin
                processing <= 1'b1;
                bit_counter <= '0;
                done <= 1'b0;
            end else if (processing) begin
                if (bit_counter == WIDTH-1) begin
                    processing <= 1'b0;
                    done <= 1'b1;
                end else begin
                    bit_counter <= bit_counter + 1'b1;
                end
            end else begin
                done <= 1'b0;
            end
        end
    end

    // Input registers
    always_ff @(posedge clk) begin
        if (!rst_n) begin
            mcand_reg <= '0;
            mplier_reg <= '0;
            partial_product <= '0;
        end else if (start && !processing) begin
            // BUG: Incorrect multiplier extension
            mcand_reg <= multiplicand;
            mplier_reg <= {multiplier, 1'b0};  // Should handle sign extension
            partial_product <= '0;
        end
    end

    // Booth encoding logic
    // BUG: Incorrect Booth encoding implementation
    always_comb begin
        booth_encoding = mplier_reg[1:0];
        case (booth_encoding)
            2'b00, 2'b11: booth_multiple = '0;                    // +0
            2'b01:        booth_multiple = mcand_reg;            // +M
            2'b10:        booth_multiple = (~mcand_reg + 1'b1);  // -M
            default:      booth_multiple = '0;
        endcase
    end

    // Partial product calculation
    // BUG: Missing pipeline stages for timing
    always_ff @(posedge clk) begin
        if (processing) begin
            // BUG: Incorrect partial product update
            partial_product <= {partial_product[2*WIDTH-1:0], 1'b0};
            case (booth_encoding)
                2'b01: partial_product[2*WIDTH:WIDTH] <= partial_product[2*WIDTH:WIDTH] + booth_multiple;
                2'b10: partial_product[2*WIDTH:WIDTH] <= partial_product[2*WIDTH:WIDTH] - booth_multiple;
                default: ; // No operation
            endcase
            // BUG: Missing sign extension handling
            mplier_reg <= {1'b0, mplier_reg[WIDTH:1]};
        end
    end

    // Final product assignment
    // BUG: Incorrect product truncation
    assign product = partial_product[2*WIDTH-1:0];

    // Assertions
    property valid_booth_encoding;
        @(posedge clk) disable iff (!rst_n)
        processing |-> (booth_encoding inside {2'b00, 2'b01, 2'b10, 2'b11});
    endproperty
    assert property (valid_booth_encoding) else $error("Invalid Booth encoding!");

    // BUG: Missing assertions for:
    // - Sign extension verification
    // - Multiplication result validation
    // - Control signal timing
    // - Pipeline stage verification
    // - Overflow detection

    // Verification helper logic
    logic signed [2*WIDTH-1:0] expected_product;
    always_comb begin
        expected_product = $signed(multiplicand) * $signed(multiplier);
    end

endmodule 