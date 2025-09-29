`default_nettype none
`include "verification/svas.sv"
`include "cov.svh"

module top_tb;
  localparam int W = 8;
  localparam logic [W-1:0] MaxVal = {W{1'b1}};

  logic clk;
  logic rst_n;
  logic [W-1:0] a;
  logic [W-1:0] b;
  logic [W-1:0] y;

  int seed;

  cg_sum cov = new();

  top dut (
      .clk  (clk),
      .rst_n(rst_n),
      .a    (a),
      .b    (b),
      .y    (y)
  );

  initial clk = 1'b0;
  always #5 clk = ~clk;

  initial begin
    if (!$value$plusargs("seed=%d", seed)) begin
      seed = 1234;
    end
    void'($urandom(seed));
    $display("[META] SEED=%0d", seed);
  end

  svas #(
      .WIDTH(W)
  ) svas_i (
      .clk (clk),
      .rst_n(rst_n),
      .a   (a),
      .b   (b),
      .y   (y)
  );

  task automatic cov_sample(string rid, input logic [W-1:0] ai, input logic [W-1:0] bi);
    $display("[COV] %s sample a=%0d b=%0d", rid, ai, bi);
  endtask

  task automatic check_sum(string rid, input logic [W-1:0] ai, input logic [W-1:0] bi);
    logic [W-1:0] exp;
    begin
      a = ai;
      b = bi;
      cov_sample(rid, ai, bi);
      @(posedge clk);
      exp = ai + bi;
      if (y !== exp) begin
        $error("[%s] Mismatch: a=%0d b=%0d got=%0d exp=%0d", rid, ai, bi, y, exp);
        $display("[META] TIME=%0t", $time);
      end else begin
        $display("[%s] PASS a=%0d b=%0d y=%0d", rid, ai, bi, y);
      end

      if (rid == "R1") begin
        cov.sample();
        $display("[COVBIN] %s a=%0d b=%0d", rid, ai, bi);
      end
    end
  endtask

  initial begin
    // R2: reset behaviour
    rst_n = 1'b0;
    a = '0;
    b = '0;
    repeat (2) @(posedge clk);
    rst_n = 1'b1;
    @(posedge clk);
    if (y !== '0) begin
      $error("[R2] Reset failed: y=%0d", y);
      $display("[META] TIME=%0t", $time);
    end else begin
      cov_sample("R2", a, b);
      $display("[R2] PASS y=%0d after reset", y);
    end

    // R1 directed checks
    check_sum("R1", W'(0), W'(0));
    check_sum("R1", W'(8'd1), W'(8'd2));
    check_sum("R3", MaxVal, W'(1));
    check_sum("R1", W'(8'hAA), W'(8'h55));

    // R1 random burst
    repeat (32) begin
      logic [W-1:0] rand_a = W'($urandom());
      logic [W-1:0] rand_b = W'($urandom());
      check_sum("R1", rand_a, rand_b);
    end

    $display("TB DONE");
    $finish;
  end
endmodule
`default_nettype wire
