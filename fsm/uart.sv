// Buggy UART Controller


module uart_controller #(
    parameter CLK_FREQ = 50000000,  // 50 MHz
    parameter BAUD_RATE = 115200    // 115.2k baud
)(
    input  logic        clk,
    input  logic        rst_n,
    // Transmit interface
    input  logic [7:0]  tx_data,
    input  logic        tx_valid,
    output logic        tx_ready,
    // Receive interface
    output logic [7:0]  rx_data,
    output logic        rx_valid,
    input  logic        rx_ready,
    // Serial interface
    input  logic        rx_in,
    output logic        tx_out,
    // Error flags
    output logic        frame_error,
    output logic        parity_error,
    output logic        overflow_error
);

    // Baud rate generator
    // BUG: Incorrect clock divider calculation
    localparam CLKS_PER_BIT = CLK_FREQ / BAUD_RATE;  // Should round to nearest integer
    logic [$clog2(CLKS_PER_BIT):0] baud_counter;
    logic baud_tick;

    // BUG: Missing clock enable logic
    always_ff @(posedge clk) begin
        if (!rst_n) begin
            baud_counter <= '0;
            baud_tick <= 1'b0;
        end else begin
            if (baud_counter == CLKS_PER_BIT - 1) begin
                baud_counter <= '0;
                baud_tick <= 1'b1;
            end else begin
                baud_counter <= baud_counter + 1'b1;
                baud_tick <= 1'b0;
            end
        end
    end

    // Transmitter FSM
    typedef enum logic [2:0] {
        TX_IDLE    = 3'b000,
        TX_START   = 3'b001,
        TX_DATA    = 3'b010,
        TX_PARITY  = 3'b011,
        TX_STOP    = 3'b100
    } tx_state_t;

    tx_state_t tx_state;
    logic [2:0] tx_bit_count;
    logic [7:0] tx_shift_reg;
    logic tx_parity;

    // BUG: Incorrect transmitter state machine
    always_ff @(posedge clk) begin
        if (!rst_n) begin
            tx_state <= TX_IDLE;
            tx_bit_count <= '0;
            tx_shift_reg <= '0;
            tx_out <= 1'b1;
            tx_ready <= 1'b1;
            tx_parity <= 1'b0;
        end else if (baud_tick) begin
            case (tx_state)
                TX_IDLE: begin
                    tx_out <= 1'b1;
                    if (tx_valid) begin
                        tx_state <= TX_START;
                        tx_shift_reg <= tx_data;
                        tx_ready <= 1'b0;
                        // BUG: Missing parity calculation
                        tx_parity <= ^tx_data;
                    end
                end

                TX_START: begin
                    tx_out <= 1'b0;
                    tx_state <= TX_DATA;
                    tx_bit_count <= '0;
                end

                TX_DATA: begin
                    // BUG: Incorrect bit ordering
                    tx_out <= tx_shift_reg[0];  // Should be MSB first
                    tx_shift_reg <= {1'b0, tx_shift_reg[7:1]};
                    if (tx_bit_count == 3'b111) begin
                        tx_state <= TX_PARITY;
                    end else begin
                        tx_bit_count <= tx_bit_count + 1'b1;
                    end
                end

                TX_PARITY: begin
                    tx_out <= tx_parity;
                    tx_state <= TX_STOP;
                end

                TX_STOP: begin
                    tx_out <= 1'b1;
                    // BUG: Missing multiple stop bit support
                    tx_state <= TX_IDLE;
                    tx_ready <= 1'b1;
                end

                default: tx_state <= TX_IDLE;
            endcase
        end
    end

    // Receiver FSM
    typedef enum logic [2:0] {
        RX_IDLE    = 3'b000,
        RX_START   = 3'b001,
        RX_DATA    = 3'b010,
        RX_PARITY  = 3'b011,
        RX_STOP    = 3'b100
    } rx_state_t;

    rx_state_t rx_state;
    logic [2:0] rx_bit_count;
    logic [7:0] rx_shift_reg;
    logic rx_parity;
    logic rx_reg;  // Input synchronizer

    // BUG: Insufficient input synchronization
    always_ff @(posedge clk) begin
        rx_reg <= rx_in;
    end

    // BUG: Incorrect receiver state machine
    always_ff @(posedge clk) begin
        if (!rst_n) begin
            rx_state <= RX_IDLE;
            rx_bit_count <= '0;
            rx_shift_reg <= '0;
            rx_valid <= 1'b0;
            frame_error <= 1'b0;
            parity_error <= 1'b0;
            overflow_error <= 1'b0;
        end else if (baud_tick) begin
            case (rx_state)
                RX_IDLE: begin
                    // BUG: Missing start bit validation
                    if (!rx_reg) begin
                        rx_state <= RX_START;
                    end
                end

                RX_START: begin
                    // BUG: Missing start bit check in middle of bit
                    rx_state <= RX_DATA;
                    rx_bit_count <= '0;
                    rx_valid <= 1'b0;
                end

                RX_DATA: begin
                    // BUG: Incorrect bit ordering
                    rx_shift_reg <= {rx_reg, rx_shift_reg[7:1]};  // Should be MSB first
                    if (rx_bit_count == 3'b111) begin
                        rx_state <= RX_PARITY;
                    end else begin
                        rx_bit_count <= rx_bit_count + 1'b1;
                    end
                end

                RX_PARITY: begin
                    // BUG: Incorrect parity check
                    if (rx_reg != ^rx_shift_reg) begin
                        parity_error <= 1'b1;
                    end
                    rx_state <= RX_STOP;
                end

                RX_STOP: begin
                    // BUG: Missing stop bit validation
                    rx_state <= RX_IDLE;
                    if (!rx_ready && rx_valid) begin
                        overflow_error <= 1'b1;
                    end else begin
                        rx_data <= rx_shift_reg;
                        rx_valid <= 1'b1;
                    end
                end

                default: rx_state <= RX_IDLE;
            endcase
        end
    end

    // Assertions
    property valid_start_bit;
        @(posedge clk) disable iff (!rst_n)
        (rx_state == RX_IDLE) && !rx_reg |=> (rx_state == RX_START);
    endproperty
    assert property (valid_start_bit) else $error("Invalid start bit detection!");

    // BUG: Missing assertions for:
    // - Baud rate timing
    // - Frame format
    // - Parity checking
    // - Stop bit validation
    // - Buffer overflow conditions

endmodule 