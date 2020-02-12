#include <chrono>

#include "bdd.h"

void bench(int num_vars) {
    int repeat = 100;
    long int total = 0;
    for (int r = 0; r < repeat; r++) {
        auto start = std::chrono::high_resolution_clock::now();

        bdd_init(300000,30000);
        bdd_setvarnum(num_vars);

        bdd result = bdd_false();
        for (int i=0; i<num_vars/2; i++) {
            bdd x1 = bdd_ithvar(i);
            bdd x2 = bdd_ithvar(i + num_vars/2);
            bdd and_bdd = x1 & x2;
            bdd new_result = result | and_bdd;
            result = new_result;
        }
        bdd_done();

        auto finish = std::chrono::high_resolution_clock::now();
        long int duration = std::chrono::duration_cast<std::chrono::nanoseconds>(finish-start).count();
        total = total + duration;
        printf("\r%d...", r);
        fflush(stdout);
    }
    printf("\rbuddy_ripple_carry_adder_%d: %ld (ns)\n", num_vars, total / repeat);
}

 int main (int argc, char *argv[])
 {
     bench(4);
     bench(8);
     bench(16);
     bench(32);
 }