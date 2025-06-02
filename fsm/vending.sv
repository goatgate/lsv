// Buggy Vending Machine Controller

module vending_machine (
    input  logic        clk,
    input  logic        rst_n,
    input  logic [1:0]  coin_in,     // 00: no coin, 01: nickel, 10: dime, 11: quarter
    input  logic        product_sel,  // 0: $0.35 product, 1: $0.50 product
    input  logic        refund_req,   // Refund request
    output logic        dispense,     // Product dispense signal
    output logic [5:0]  change_out,   // Change amount in nickels
    output logic        busy          // Machine busy signal
);

    // Price definitions
    localparam PRICE_A = 7;  // $0.35 (in nickels)
    localparam PRICE_B = 10; // $0.50 (in nickels)

    // Coin values in nickels
    localparam NICKEL  = 1;
    localparam DIME    = 2;
    localparam QUARTER = 5;

    // State encoding
    // BUG: Poor state encoding choice
    typedef enum logic [2:0] {
        IDLE     = 3'b000,
        COLLECT  = 3'b001,
        DISPENSE = 3'b010,
        CHANGE   = 3'b011,
        REFUND   = 3'b100
        // BUG: Missing ERROR state
    } state_t;

    state_t current_state, next_state;
    logic [5:0] money_inserted;    // Amount inserted in nickels
    logic [5:0] required_amount;   // Required amount based on selection
    logic [5:0] change_amount;     // Amount to return

    // BUG: Incorrect money accumulation
    always_ff @(posedge clk) begin
        if (!rst_n) begin
            money_inserted <= '0;
        end else if (current_state == COLLECT) begin
            case (coin_in)
                2'b01: money_inserted <= money_inserted + NICKEL;
                2'b10: money_inserted <= money_inserted + DIME;
                2'b11: money_inserted <= money_inserted + QUARTER;
                default: money_inserted <= money_inserted;
            endcase
        end else if (current_state == REFUND || current_state == IDLE) begin
            money_inserted <= '0;
        end
    end

    // BUG: Incorrect product price selection
    always_comb begin
        required_amount = product_sel ? PRICE_B : PRICE_A;
    end

    // Next state logic
    // BUG: Complex combinational logic with potential timing issues
    always_comb begin
        next_state = current_state;
        change_amount = '0;
        dispense = 1'b0;
        busy = 1'b1;

        case (current_state)
            IDLE: begin
                busy = 1'b0;
                if (coin_in != 2'b00) begin
                    next_state = COLLECT;
                end
            end

            COLLECT: begin
                // BUG: Missing timeout handling
                if (refund_req) begin
                    next_state = REFUND;
                end else if (money_inserted >= required_amount) begin
                    next_state = DISPENSE;
                    // BUG: Incorrect change calculation
                    change_amount = money_inserted - required_amount;
                end
            end

            DISPENSE: begin
                dispense = 1'b1;
                // BUG: Missing dispense confirmation check
                next_state = CHANGE;
            end

            CHANGE: begin
                // BUG: No check if change was successfully returned
                if (change_amount == 0) begin
                    next_state = IDLE;
                end
            end

            REFUND: begin
                // BUG: Deadlock condition - no exit if refund fails
                if (money_inserted == 0) begin
                    next_state = IDLE;
                end
            end

            default: next_state = IDLE;
        endcase
    end

    // State register
    always_ff @(posedge clk) begin
        if (!rst_n) begin
            current_state <= IDLE;
        end else begin
            current_state <= next_state;
        end
    end

    // Change output
    // BUG: Combinational output without registration
    assign change_out = (current_state == CHANGE) ? change_amount :
                       (current_state == REFUND) ? money_inserted : '0;

    // Assertions
    property valid_change;
        @(posedge clk) disable iff (!rst_n)
        (current_state == CHANGE) |-> (change_out <= money_inserted);
    endproperty
    assert property (valid_change) else $error("Invalid change amount!");

    // BUG: Missing assertions for:
    // - Money accounting
    // - Product dispensing
    // - Refund handling
    // - State transitions
    // - Timeout conditions

endmodule 