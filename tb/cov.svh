/* verilator lint_off COVERIGN */
/* verilator lint_off DECLFILENAME */
/* verilator lint_off UNDRIVEN */
covergroup cg_sum @(posedge clk);
  coverpoint a {
    bins zero = {0};
    bins max = {'1};
    bins mid[] = {[1:$-1]};
  }
  coverpoint b {
    bins zero = {0};
    bins max = {'1};
    bins mid[] = {[1:$-1]};
  }
  cross a, b;
endgroup
/* verilator lint_on UNDRIVEN */
/* verilator lint_on DECLFILENAME */
/* verilator lint_on COVERIGN */
