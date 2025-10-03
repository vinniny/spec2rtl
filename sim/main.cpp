#include "Vtop_tb.h"
#include "verilated.h"
#include <cstdlib>
#include <string>
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
  const char* reports_env = std::getenv("REPORTS_DIR");
  const std::string cov_path = reports_env && reports_env[0] ?
      (std::string(reports_env) + "/coverage.dat") :
      std::string("reports/coverage.dat");
  VerilatedCov::write(cov_path.c_str());
#endif
  return context.gotFinish() ? 0 : 1;
}
