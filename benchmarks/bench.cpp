#include <cstdio>
#include <cassert>
#include <limits>
#include <climits>
#include <algorithm>
#include <cstring>
#include <cmath>
#include <cfenv>
#include <bit>
#include <vector>
#include <iostream>
#include <unordered_map>
#include <chrono>
#include <omp.h>

#include "lala/zinterval.hpp"

enum Sig { ADD, SUB, MUL, TDIV, FDIV, CDIV, EDIV };

using namespace lala;

template <class value_t>
value_t op(value_t a, Sig op, value_t b) {
  switch(op) {
    case ADD: return a + b;
    case SUB: return a - b;
    case MUL: return a * b;
    case TDIV: return battery::tdiv(a, b);
    case CDIV: return battery::cdiv(a, b);
    case FDIV: return battery::fdiv(a, b);
    case EDIV: return battery::ediv(a, b);
    default: assert(false); return a;
  }
}

/* Greatest Fixpoint */
template <class Itv, class Prop>
size_t gfp(Itv& x2, Itv& y2, Itv& z2, Prop p) {
  Itv x3, y3, z3;
  size_t iter = 0;
  do {
    x3 = x2;
    y3 = y2;
    z3 = z2;
    p(x2, y2, z2);
    // std::cout << x2 << " " << y2 << " " << z2 << std::endl;
    iter++;
  } while(!(x2.is_bot() || y2.is_bot() || z2.is_bot()) && (x2 != x3 || y2 != y3 || z2 != z3));
  return iter;
}

/* CONCRETE PROPAGATION. */

bool is_div(Sig sig) {
  return sig == TDIV || sig == CDIV || sig == FDIV || sig == EDIV;
}

template <class Itv>
size_t concrete_propagation(Sig sig, Itv& r1, Itv& r2, Itv& r3) {
  Itv x2 = Itv::bot();
  Itv y2 = Itv::bot();
  Itv z2 = Itv::bot();
  size_t num_sol = 0;
  for(int b = r2.lb(); b <= r2.ub(); ++b) {
    for(int c = r3.lb(); c <= r3.ub(); ++c) {
      if((!is_div(sig) || c != 0)) {
        int a = op(b, sig, c);
        if(r1.contains(a)) {
          x2.join(Itv(a,a));
          y2.join(Itv(b,b));
          z2.join(Itv(c,c));
          num_sol++;
        }
      }
    }
  }
  r1.meet(x2);
  r2.meet(y2);
  r3.meet(z2);
  return num_sol;
}

struct Statistics {
  size_t bottom_propagations;
  size_t idempotent_propagations;
  size_t bottom_concrete;
  size_t incomplete_ask;
  int64_t abstract_propag_ns;
  int64_t concrete_propag_ns;
  std::unordered_map<size_t, size_t> fp_iterations;
  Statistics() : abstract_propag_ns(0), concrete_propag_ns(0), idempotent_propagations(0), bottom_propagations(0), bottom_concrete(0), incomplete_ask(0) {}
  void merge(const Statistics& other) {
    abstract_propag_ns += other.abstract_propag_ns;
    concrete_propag_ns += other.concrete_propag_ns;
    idempotent_propagations += other.idempotent_propagations;
    bottom_propagations += other.bottom_propagations;
    bottom_concrete += other.bottom_concrete;
    incomplete_ask += other.incomplete_ask;
    for(const auto& [iter, count] : other.fp_iterations) {
      fp_iterations[iter] += count;
    }
  }

  void print(size_t total) {
    std::cout << "  Total concrete propagation time (ms): " << concrete_propag_ns / 1000000 << std::endl;
    std::cout << "  Total abstract propagation time (ms): " << abstract_propag_ns / 1000000 << std::endl;
    for(const auto& [iter, count] : fp_iterations) {
      printf("  Iterations to fixpoint: %zu, Count: %zu\n", iter, count);
    }
    printf("Bottom propagations: %zu (%.2f%%)\n", bottom_propagations, 100.0 * (double)bottom_propagations / (double)total);
    printf("Bottom concrete propagations: %zu (%.2f%%)\n", bottom_concrete, 100.0 * (double)bottom_concrete / (double)total);
    printf("Idempotent propagations: %zu (%.2f%%)\n", idempotent_propagations, 100.0 * (double)idempotent_propagations / (double)total);
    printf("Incomplete ask: %zu (%.2f%%)\n", incomplete_ask, 100.0 * (double)incomplete_ask / (double)total);
    printf("Double propagations: %zu (%.2f%%)\n", fp_iterations[1] + fp_iterations[2], 100.0 * (double)( fp_iterations[1]+fp_iterations[2]) / (double)total);
    printf("Triple propagations: %zu (%.2f%%)\n", fp_iterations[1] + fp_iterations[2] + fp_iterations[3], 100.0 * (double)( fp_iterations[1]+fp_iterations[2]+fp_iterations[3]) / (double)total);
  }

  void print_csv(size_t total) {
    std::string iters = "\"{";
    for(const auto& [iter, count] : fp_iterations) {
      iters += std::to_string(iter) + ":" + std::to_string(count) + ",";
    }
    iters.pop_back();
    iters += "}\"";
    std::cout << (concrete_propag_ns / 1000000) << "," << (abstract_propag_ns / 1000000) << ",";
    std::cout << bottom_propagations << "," << (100.0 * (double)bottom_propagations / (double)total) << ",";
    std::cout << bottom_concrete << "," << (100.0 * (double)bottom_concrete / (double)total) << ",";
    std::cout << idempotent_propagations << "," << (100.0 * (double)idempotent_propagations / (double)total) << ",";
    std::cout << incomplete_ask << "," << (100.0 * (double)incomplete_ask / (double)total) << ",";
    std::cout << iters;
  }
};

template <class Itv, class Prop, class Ask>
int propagate(Sig sig, Itv x, Itv y, Itv z,
              Statistics& stats, Prop p, Ask ask)
{
  int not_best = 0;

  Itv x2(x);
  Itv y2(y);
  Itv z2(z);

  // Compute the concrete intervals.
  Itv cx(x);
  Itv cy(y);
  Itv cz(z);

  auto start = std::chrono::steady_clock::now();
  size_t concrete_num_sols = concrete_propagation(sig, cx, cy, cz);
  auto end = std::chrono::steady_clock::now();
  stats.concrete_propag_ns += std::chrono::duration_cast<std::chrono::nanoseconds>(end - start).count();

  // Compute the abstract intervals.
  start = std::chrono::steady_clock::now();
  size_t iter = gfp(x, y, z, p);
  end = std::chrono::steady_clock::now();
  // printf("  Abstract x=[%d,%d] y=[%d,%d] z=[%d,%d]\n", x.lb(), x.ub(), y.lb(), y.ub(), z.lb(), z.ub());
  stats.abstract_propag_ns += std::chrono::duration_cast<std::chrono::nanoseconds>(end - start).count();
  stats.fp_iterations[iter]++;
  if(iter == 1 || (iter == 2 && !(x.is_bot() || y.is_bot() || z.is_bot()))) {
    stats.idempotent_propagations++;
  }
  bool abstract_bot = x.is_bot() || y.is_bot() || z.is_bot();
  stats.bottom_propagations += abstract_bot ? 1 : 0;
  bool concrete_bot = cx.is_bot() || cy.is_bot() || cz.is_bot();
  stats.bottom_concrete += concrete_bot ? 1 : 0;

  // Check soundness of entailment (ask operation)
  size_t abstract_num_sols = size_t{x.count().load()} * size_t{y.count().load()} * size_t{z.count().load()};
  if(ask(x, y, z)) {
    if(abstract_num_sols != concrete_num_sols) {
      std::cout << "Unsound ask operation for x=" << x2 << " y=" << y2 << " z=" << z2 << std::endl;
      std::cout << "\tConcrete x=" << cx << " y=" << cy << " z=" << cz << " total solutions: " << concrete_num_sols << std::endl;
      std::cout << "\tAbstract x=" << x << " y=" << y << " z=" << z << " total solutions: " << abstract_num_sols << std::endl;
    }
  }
  // Check completeness of entailment (ask operation)
  else {
    size_t concrete_num_sols2 = size_t{cx.count().load()} * size_t{cy.count().load()} * size_t{cz.count().load()};
    if(concrete_num_sols == concrete_num_sols2) {
      stats.incomplete_ask++;
      // std::cout << "Incomplete ask operation for x=" << x2 << " y=" << y2 << " z=" << z2 << std::endl;
      // std::cout << "\tConcrete x=" << cx << " y=" << cy << " z=" << cz << " total solutions: " << concrete_num_sols << std::endl;
      // std::cout << "\tAbstract x=" << x << " y=" << y << " z=" << z << " total solutions: " << abstract_num_sols << std::endl;
    }
  }

  // If they are both at bottom, the propagator is sound and complete on the tested values.
  if(!(abstract_bot && concrete_bot)) {
    // Check soundness.
    if(abstract_bot || !(x.contains(cx) && y.contains(cy) && z.contains(cz))) {
      std::cout << "Unsound propagator for x=" << x2 << " y=" << y2 << " z=" << z2 << std::endl;
      std::cout << "\tConcrete x=" << cx << " y=" << cy << " z=" << cz << std::endl;
      std::cout << "\tAbstract x=" << x << " y=" << y << " z=" << z << std::endl;
      exit(1);
    }
    // Check best propagator.
    else if(cx != x || cy != y || cz != z) {
      // Check completeness on singleton
      if(x.is_singleton() && y.is_singleton() && z.is_singleton()) {
        std::cout << "Incomplete propagator on singleton for x=" << x2 << " y=" << y2 << " z=" << z2 << std::endl;
        std::cout << "\tConcrete x=" << cx << " y=" << cy << " z=" << cz << std::endl;
        std::cout << "\tAbstract x=" << x << " y=" << y << " z=" << z << std::endl;
        exit(1);
      }
      else {
        // if(not_best < 100) {
        // if(concrete_bot) {
          // printf("Sound but not the best propagator for x=[%d,%d] y=[%d,%d] z=[%d,%d]\n", x.lb(), x.ub(), y.lb(), y.ub(), z.lb(), z.ub());
          // printf("  Concrete x=[%d,%d] y=[%d,%d] z=[%d,%d]\n", cx.lb(), cx.ub(), cy.lb(), cy.ub(), cz.lb(), cz.ub());
          // printf("  Abstract x=[%d,%d] y=[%d,%d] z=[%d,%d]\n", x.lb(), x.ub(), y.lb(), y.ub(), z.lb(), z.ub());
        // }
        // exit(1);
        ++not_best;
      }
    }
  }
  return not_best;
}

enum PropKind {
  BASIC_ADD,
  BASIC_SUB,
  BASIC_MUL,
  BASIC_DIV,
  SPLITY_DIV,
  SPLITZ_DIV,
  DIV_SPLITY_DIV,
  DIV_SPLITZ_DIV,
  DIV_SPLITY_GFP_DIV,
  DIV_SPLITZ_GFP_DIV
};

const char* sig_to_string(Sig sig) {
  switch(sig) {
    case ADD: return "ADD";
    case SUB: return "SUB";
    case MUL: return "MUL";
    case FDIV: return "FDIV";
    case CDIV: return "CDIV";
    case TDIV: return "TDIV";
    case EDIV: return "EDIV";
    default: return "UNKNOWN_SIG";
  }
}

const char* prop_kind_to_string(PropKind prop_kind) {
  switch(prop_kind) {
    case BASIC_ADD: return "BASIC_ADD";
    case BASIC_SUB: return "BASIC_SUB";
    case BASIC_MUL: return "BASIC_MUL";
    case BASIC_DIV: return "BASIC_DIV";
    case SPLITY_DIV: return "SPLITY_DIV";
    case SPLITZ_DIV: return "SPLITZ_DIV";
    case DIV_SPLITY_DIV: return "DIV_SPLITY_DIV";
    case DIV_SPLITZ_DIV: return "DIV_SPLITZ_DIV";
    case DIV_SPLITY_GFP_DIV: return "DIV_SPLITY_GFP_DIV";
    case DIV_SPLITZ_GFP_DIV: return "DIV_SPLITZ_GFP_DIV";
    default: return "UNKNOWN_PROP_KIND";
  }
}

template <class Itv>
void benchmark(const char* itv_name, bool csv) {
  using value_type = typename Itv::value_type;

  // Statistics fake;
  // propagate(ADD, Itv(-2,-2), Itv(0,0), Itv(-2,-1), fake, tell::zadd<value_type>);
  // printf("--\n");
  // exit(1);

  std::vector<std::tuple<Sig, PropKind>> prop_kinds = {
    {ADD, BASIC_ADD},
    {SUB, BASIC_SUB},
    {MUL, BASIC_MUL},
    {FDIV, BASIC_DIV},
    {CDIV, BASIC_DIV},
    {TDIV, BASIC_DIV},
    {EDIV, BASIC_DIV},
  };
  for(auto [sig, prop_kind] : prop_kinds) {
    std::vector<Statistics> stats_list(omp_get_max_threads());
    size_t not_best = 0;
    size_t total = 0;
    std::unordered_map<size_t, size_t> fp_iterations;
    int64_t abstract_propag_ns = 0;
    int64_t concrete_propag_ns = 0;
    // int max = 40;
    // for(int bound = 0; bound <= max; ++bound) {
    if(true) { int bound = 10;
      Itv x = Itv(-bound, bound);
      Itv y = Itv(-bound, bound);
      Itv z = Itv(-bound, bound);

      // #pragma omp parallel for collapse(4) schedule(dynamic)
      for(int xl = x.lb(); xl <= x.ub(); ++xl) {
      for(int xu = x.lb(); xu <= x.ub(); ++xu) {
      for(int yl = y.lb(); yl <= y.ub(); ++yl) {
      for(int yu = y.lb(); yu <= y.ub(); ++yu) {
      if(xu < xl || yu < yl) { continue; } // For easy parallelisation with OpenMP (and use collapse(4)).
      for(int zl = z.lb(); zl <= z.ub(); ++zl) {
      for(int zu = zl; zu <= z.ub(); ++zu) {
        // Skip values that were already tested with smaller bounds.
        Itv prev(-(bound - 1), bound - 1);
        if(Itv(xl, xu).leq(prev) && Itv(yl, yu).leq(prev) && Itv(zl, zu).leq(prev)) {
          continue;
        }
        int r = 0;
        switch(sig) {
          case ADD: r = propagate(sig, Itv(xl, xu), Itv(yl, yu), Itv(zl, zu), stats_list[omp_get_thread_num()], tell::zadd<value_type>, ask::zadd<value_type>); break;
          case SUB: r = propagate(sig, Itv(xl, xu), Itv(yl, yu), Itv(zl, zu), stats_list[omp_get_thread_num()], tell::zsub<value_type>, ask::zsub<value_type>); break;
          case MUL: r = propagate(sig, Itv(xl, xu), Itv(yl, yu), Itv(zl, zu), stats_list[omp_get_thread_num()], tell::zmul<value_type>, ask::zmul<value_type>); break;
          case FDIV: r = propagate(sig, Itv(xl, xu), Itv(yl, yu), Itv(zl, zu), stats_list[omp_get_thread_num()], tell::fdiv<value_type>, ask::fdiv<value_type>); break;
          case CDIV: r = propagate(sig, Itv(xl, xu), Itv(yl, yu), Itv(zl, zu), stats_list[omp_get_thread_num()], tell::cdiv<value_type>, ask::cdiv<value_type>); break;
          case TDIV: r = propagate(sig, Itv(xl, xu), Itv(yl, yu), Itv(zl, zu), stats_list[omp_get_thread_num()], tell::tdiv<value_type>, ask::tdiv<value_type>); break;
          case EDIV: r = propagate(sig, Itv(xl, xu), Itv(yl, yu), Itv(zl, zu), stats_list[omp_get_thread_num()], tell::ediv<value_type>, ask::ediv<value_type>); break;
          default: printf("ERROR!\n"); exit(1);
        }
        #pragma omp atomic
        not_best += r;
        #pragma omp atomic
        total++;
      }}}}}}

      Statistics stats;

      for(size_t i = 0; i < stats_list.size(); ++i) {
        stats.merge(stats_list[i]);
      }

      if(csv) {
        printf("%s,%s,%s,%d,%zu,%zu,%.2f,%zu,%.2f,", itv_name, sig_to_string(sig), prop_kind_to_string(prop_kind), 2*bound+1, total, not_best, 100.0 * (double(not_best) / double(total)), total-not_best, 100.0 * (double(total-not_best) / double(total)));
        stats.print_csv(total);
        printf("\n");
        std::cout << std::flush;
      }
      else {
        printf("%s %s (%s): ", itv_name, sig_to_string(sig), prop_kind_to_string(prop_kind));
        printf("Sound and complete on singleton.\n");
        printf("Not the best on %zu examples for %zu tested (%.2f%%).\n", not_best, total, 100.0 * (double(not_best) / double(total)));
        printf("The best on %zu examples for %zu tested (%.2f%%).\n", total-not_best, total, 100.0 * (double(total-not_best) / double(total)));
        stats.print(total);
        std::cout << std::flush;
      }
    }
  }
}

int main(int argc, char** argv) {
  bool csv = false;
  if(csv) {
    printf("abstract_domain,operation,propagator,width,total,not_best,not_best_percentage,best,best_percentage,concrete_time_ms,abstract_time_ms,bottom_propagations,bottom_propagations_percent,bottom_concrete_propagations,bottom_concrete_propagations_percent,idempotent_propagations,idempotent_propagations_percent,incomplete_ask,incomplete_ask_percent,fixpoint_iterations_dict\n");
  }
  benchmark<ZInterval<int>>("ZInterval<int>", csv);
  benchmark<ZInterval<long long>>("ZInterval<long long>", csv);
  benchmark<ZInterval<float>>("ZInterval<float>", csv);
  benchmark<ZInterval<double>>("ZInterval<double>", csv);
  return 0;
}

// g++ -std=c++23 -O3 -march=native -fopenmp -I ../include/ -I ../../cuda-battery/include/ bench.cpp
