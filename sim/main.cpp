#include "Vtop_tb.h"
#include "verilated.h"
#ifdef VM_COVERAGE
#include "verilated_cov.h"
#endif
#include "verilated_timing.h"

int main(int argc, char** argv) {
  VerilatedContext context;
  context.commandArgs(argc, argv);
  Vtop_tb tb{&context};

  const uint64_t kMaxTime = 5000;
  while (!context.gotFinish()) {
    tb.eval_step();
    tb.eval_end_step();

    if (!tb.eventsPending()) {
      break;
    }

    const uint64_t next_time = tb.nextTimeSlot();
    if (next_time > kMaxTime) {
      context.time(kMaxTime);
      break;
    }

    context.time(next_time);
  }

  tb.final();

#ifdef VM_COVERAGE
  VerilatedCov::write("reports/coverage.dat");
#endif
  return context.gotFinish() ? 0 : 1;
}
