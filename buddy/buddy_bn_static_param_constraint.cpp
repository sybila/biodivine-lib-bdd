#include <chrono>

#include "bdd.h"


void bench_observability(int num_regulators) {
    int repeat = 100;
    int num_vars = 1 << num_regulators;
    long int total = 0;
    for (int r = 0; r < repeat; r++) {
        auto start = std::chrono::high_resolution_clock::now();

        bdd_init(16384 * num_vars, 4096 * num_vars);
        bdd_setvarnum(num_vars);

        // for some reason, Cudd_ReadZero is doing som bullshit
        bdd result = bdd_true();

        for (int input=0; input < num_regulators; input++) {
            int block_size = 1 << (input + 1);
            int half_block = block_size / 2;
            bdd regulator_formula = bdd_false();
            for (int block=0; block < (num_vars / block_size); block++) {
                for (int block_item=0; block_item < half_block; block_item++) {
                    bdd var1 = bdd_ithvar(block_size * block + block_item);
                    bdd var2 = bdd_ithvar(block_size * block + block_item + half_block);
                    bdd tmp = !((var1 & var2) | (!var1 & !var2));
                    bdd tmp_r = regulator_formula | tmp;
                    regulator_formula = tmp_r;
                }
            }
            bdd tmp = result & regulator_formula;
            result = tmp;
        }
        bdd_done();

        auto finish = std::chrono::high_resolution_clock::now();
        long int duration = std::chrono::duration_cast<std::chrono::nanoseconds>(finish-start).count();
        total = total + duration;
        printf("\r%d...", r);
        fflush(stdout);
    }
    printf("\rbuddy_bn_parametrised_observability_%d: %ld (ns)\n", num_regulators, total / repeat);
}

void bench_activation(int num_regulators) {
    int repeat = 100;
    int num_vars = 1 << num_regulators;
    long int total = 0;
    for (int r = 0; r < repeat; r++) {
        auto start = std::chrono::high_resolution_clock::now();

        bdd_init(16384 * num_vars, 4096 * num_vars);
        bdd_setvarnum(num_vars);

        // for some reason, Cudd_ReadZero is doing som bullshit
        bdd result = bdd_true();

        for (int input=0; input < num_regulators; input++) {
            int block_size = 1 << (input + 1);
            int half_block = block_size / 2;
            // fake zero...
            bdd regulator_formula = bdd_true();
            for (int block=0; block < (num_vars / block_size); block++) {
                for (int block_item=0; block_item < half_block; block_item++) {
                    bdd var1 = bdd_ithvar(block_size * block + block_item);
                    bdd var2 = bdd_ithvar(block_size * block + block_item + half_block);
                    bdd tmp = !var1 | var2;
                    bdd tmp_r = regulator_formula & tmp;
                    regulator_formula = tmp_r;
                }
            }
            bdd tmp = result & regulator_formula;
            result = tmp;
        }
        bdd_done();

        auto finish = std::chrono::high_resolution_clock::now();
        long int duration = std::chrono::duration_cast<std::chrono::nanoseconds>(finish-start).count();
        total = total + duration;
        printf("\r%d...", r);
        fflush(stdout);
    }
    printf("\rbuddy_bn_parametrised_activation_%d: %ld (ns)\n", num_regulators, total / repeat);
}

int main (int argc, char *argv[])
{
    bench_observability(4);
    bench_observability(5);
    bench_activation(4);
    bench_activation(5);
}