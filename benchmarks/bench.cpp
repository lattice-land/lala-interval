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
#include <random>
#include <omp.h>

#include "lala/zinterval.hpp"
#include "lala/finterval.hpp"

enum Sig { ADD, SUB, MULDIV, MUL, TDIV, FDIV, CDIV, EDIV, MIN, MAX, RLEQ, REQ };

using namespace lala;

template <class value_t>
value_t op(value_t a, Sig op, value_t b) {
  switch(op) {
    case ADD: return a + b;
    case SUB: return a - b;
    case MULDIV:
    case MUL: return a * b;
    case TDIV: return battery::tdiv(a, b);
    case CDIV: return battery::cdiv(a, b);
    case FDIV: return battery::fdiv(a, b);
    case EDIV: return battery::ediv(a, b);
    case MIN: return battery::min(a, b);
    case MAX: return battery::max(a, b);
    case REQ: return a == b ? 1 : 0;
    case RLEQ: return a <= b ? 1 : 0;
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
  using VT = typename Itv::value_type;
  Itv x2 = Itv::bot();
  Itv y2 = Itv::bot();
  Itv z2 = Itv::bot();
  size_t num_sol = 0;
  for(VT b = r2.lb(); b <= r2.ub(); ++b) {
    for(VT c = r3.lb(); c <= r3.ub(); ++c) {
      if((!is_div(sig) || c != 0)) {
        VT a = op(b, sig, c);
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
              Statistics& stats, Prop p, Ask ask, bool compute_gfp = true)
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
  size_t iter = 1;
  if(compute_gfp) {
    iter = gfp(x, y, z, p);
  }
  else {
    p(x, y, z);
  }
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
          // std::cout << "Sound but not the best propagator for x=" << x2 << " y=" << y2 << " z=" << z2 << std::endl;
          // std::cout << "\tConcrete x=" << cx << " y=" << cy << " z=" << cz << std::endl;
          // std::cout << "\tAbstract x=" << x << " y=" << y << " z=" << z << std::endl;
        // }
        // exit(1);
        ++not_best;
      }
    }
  }
  return not_best;
}

enum PropKind {
  FP,
  FDP,
  FXP,
  FDPP,
  FDFP,
  FXFP,
  FULLSPLIT,
  DPP,
  DP,
  P,
  PP,
};

const char* sig_to_string(Sig sig) {
  switch(sig) {
    case ADD: return "ADD";
    case SUB: return "SUB";
    case MUL: return "MUL";
    case MULDIV: return "MULDIV";
    case FDIV: return "FDIV";
    case CDIV: return "CDIV";
    case TDIV: return "TDIV";
    case EDIV: return "EDIV";
    case MIN: return "MIN";
    case MAX: return "MAX";
    case RLEQ: return "RLEQ";
    case REQ: return "REQ";
    default: return "UNKNOWN_SIG";
  }
}

const char* prop_kind_to_string(PropKind prop_kind) {
  switch(prop_kind) {
    case FP: return "FP";
    case FDP: return "FDP";
    case FXP: return "FXP";
    case FDPP: return "FDPP";
    case FDFP: return "FDFP";
    case FXFP: return "FXFP";
    case FULLSPLIT: return "FULLSPLIT";
    case DPP: return "DPP";
    case DP: return "DP";
    case P: return "P";
    case PP: return "PP";
    default: return "UNKNOWN_PROP_KIND";
  }
}

template <class Itv, class Prop, class Ask>
int wrap_propagate(PropKind prop_kind, Sig sig, Itv x, Itv y, Itv z,
              Statistics& stats, Prop p, Ask ask)
{
  using VT = typename Itv::value_type;
  switch(prop_kind) {
    case P: return propagate(sig, x, y, z, stats, p, ask, false);
    case PP: return propagate(sig, x, y, z, stats,
      [&p](Itv& x, Itv& y, Itv& z) { p(x, y, z); p(x, y, z); },
      ask, false);
    case FP: return propagate(sig, x, y, z, stats, p, ask);
    case FDP: return propagate(sig, x, y, z, stats,
      [&p](Itv& x, Itv& y, Itv& z) { tell::splitjoin(x, y, z, z, VT{0}, p); },
      ask);
    case FXP: return propagate(sig, x, y, z, stats,
      [&p](Itv& x, Itv& y, Itv& z) { tell::splitjoin(x, y, z, x, VT{0}, p); },
      ask);
    case DP: return propagate(sig, x, y, z, stats,
      [&p](Itv& x, Itv& y, Itv& z) { tell::splitjoin(x, y, z, z, VT{0}, p); },
      ask,
      false);
    case FDPP: return propagate(sig, x, y, z, stats,
      [&p](Itv& x, Itv& y, Itv& z) { tell::splitjoin(x, y, z, z, VT{0},
        [&p](Itv& x, Itv& y, Itv& z) { p(x, y, z); p(x, y, z); }); },
      ask);
    case FDFP: return propagate(sig, x, y, z, stats,
      [&p](Itv& x, Itv& y, Itv& z) { tell::splitjoin(x, y, z, z, VT{0},
        [&p](Itv& x, Itv& y, Itv& z) { gfp(x, y, z, p); }); },
      ask);
    case FXFP: return propagate(sig, x, y, z, stats,
      [&p](Itv& x, Itv& y, Itv& z) { tell::splitjoin(x, y, z, x, VT{0},
        [&p](Itv& x, Itv& y, Itv& z) { gfp(x, y, z, p); }); },
      ask);
    case FULLSPLIT: return propagate(sig, x, y, z, stats,
      [&p](Itv& x, Itv& y, Itv& z) { tell::splitjoin(x, y, z, y, y.lb().load(),
        [&p](Itv& x, Itv& y, Itv& z) { gfp(x, y, z,
        [&p](Itv& x, Itv& y, Itv& z) { tell::splitjoin(x, y, z, x, x.lb().load(),
          [&p](Itv& x, Itv& y, Itv& z) { gfp(x,y,z,p); }); }); }); },
      ask);
    case DPP: return propagate(sig, x, y, z, stats,
      [&p](Itv& x, Itv& y, Itv& z) { tell::splitjoin(x, y, z, z, VT{0},
        [&p](Itv& x, Itv& y, Itv& z) { p(x, y, z); p(x, y, z); }); },
      ask,
      false);
    default: assert(0); printf("unknown propagator kind.\n"); return 0;
  }
}

template <class Itv>
void benchmark(const char* itv_name, bool csv) {
  using value_type = typename Itv::value_type;

  // Statistics fake;
  // propagate(FDIV, Itv(-2,-1), Itv(0,1), Itv(-2,-2), fake,
  //   boundr::tell::zfdiv<FInterval<double>, value_type>,
  //   ask::zfdiv<value_type>);
  // printf("--\n");
  // exit(1);

  constexpr bool boundr = true;
  std::vector<std::tuple<Sig, PropKind>> prop_kinds = {
    // {ADD, P},
    // {SUB, P},
    // {MUL, FP},
    // {MUL, FDP},
    // {MULDIV, FP},
    // {TDIV, FP},
    {TDIV, FDP},
    // {FDIV, FP},
    {FDIV, FDP},
    // {CDIV, FP},
    {CDIV, FDP},
    // {EDIV, FP},
    {EDIV, FDP},
    // {FDIV, DP},
    // {FDIV, DP},
    // {CDIV, DP},
    // {TDIV, DP},
    // {EDIV, DP},
    // {MIN, P},
    // {MAX, P},
    // {REQ, FP},
    // {RLEQ, FP},
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
    if(true) { int bound = 15;
      Itv x = Itv(-bound, bound);
      Itv y = Itv(-bound, bound);
      Itv z = Itv(-bound, bound);

      int xub = static_cast<int>(x.ub());
      int yub = static_cast<int>(y.ub());

      #pragma omp parallel for collapse(4) schedule(dynamic)
      for(int xl = x.lb(); xl <= xub; ++xl) {
      for(int xu = x.lb(); xu <= xub; ++xu) {
      for(int yl = y.lb(); yl <= yub; ++yl) {
      for(int yu = y.lb(); yu <= yub; ++yu) {
      if(xu < xl || yu < yl) { continue; } // For easy parallelisation with OpenMP (and use collapse(4)).
      for(int zl = z.lb(); zl <= z.ub(); ++zl) {
      for(int zu = zl; zu <= z.ub(); ++zu) {
        // Skip values that were already tested with smaller bounds.
        // Itv prev(-(bound - 1), bound - 1);
        // if(Itv(xl, xu).leq(prev) && Itv(yl, yu).leq(prev) && Itv(zl, zu).leq(prev)) {
        //   continue;
        // }
        int r = 0;
        switch(sig) {
          case ADD: r = wrap_propagate(prop_kind, sig, Itv(xl, xu), Itv(yl, yu), Itv(zl, zu), stats_list[omp_get_thread_num()],
            boundr ? boundr::tell::zadd<FInterval<double>, value_type> : tell::zadd<value_type>,
            boundr ? boundr::ask::zadd<FInterval<double>, value_type> : ask::zadd<value_type>);
            break;
          case SUB: r = wrap_propagate(prop_kind, sig, Itv(xl, xu), Itv(yl, yu), Itv(zl, zu), stats_list[omp_get_thread_num()],
            boundr ? boundr::tell::zsub<FInterval<double>, value_type> : tell::zsub<value_type>,
            boundr ? boundr::ask::zsub<FInterval<double>, value_type> : ask::zsub<value_type>); break;
          case MUL: r = wrap_propagate(prop_kind, sig, Itv(xl, xu), Itv(yl, yu), Itv(zl, zu), stats_list[omp_get_thread_num()],
            boundr ? boundr::tell::zmul<FInterval<double>, value_type> : tell::zmul<value_type>,
            boundr ? boundr::ask::zmul<FInterval<double>, value_type> : ask::zmul<value_type>); break;
          case MULDIV: r = wrap_propagate(prop_kind, sig, Itv(xl, xu), Itv(yl, yu), Itv(zl, zu), stats_list[omp_get_thread_num()],
            [](auto& x, auto& y, auto& z) {
              if(!x.contains(0) || !z.contains(0)) {
                tell::zfdiv<value_type>(y, x, z);
                tell::zcdiv<value_type>(y, x, z);
              }
              if(!x.contains(0) || !y.contains(0)) {
                tell::zfdiv<value_type>(z, x, y);
                tell::zcdiv<value_type>(z, x, y);
              }
            },
            ask::zmul<value_type>); break;
          case FDIV: r = wrap_propagate(prop_kind, sig, Itv(xl, xu), Itv(yl, yu), Itv(zl, zu), stats_list[omp_get_thread_num()],
            boundr ? boundr::tell::zfdiv<FInterval<double>, value_type> : tell::zfdiv_fast<value_type>,
            ask::zfdiv<value_type>); break;
          case CDIV: r = wrap_propagate(prop_kind, sig, Itv(xl, xu), Itv(yl, yu), Itv(zl, zu), stats_list[omp_get_thread_num()],
            boundr ? boundr::tell::zcdiv<FInterval<double>, value_type> : tell::zcdiv_fast<value_type>,
            ask::zcdiv<value_type>); break;
          case TDIV: r = wrap_propagate(prop_kind, sig, Itv(xl, xu), Itv(yl, yu), Itv(zl, zu), stats_list[omp_get_thread_num()],
            boundr ? boundr::tell::ztdiv<FInterval<double>, value_type> : tell::ztdiv_fast<value_type>,
            ask::ztdiv<value_type>); break;
          case EDIV: r = wrap_propagate(prop_kind, sig, Itv(xl, xu), Itv(yl, yu), Itv(zl, zu), stats_list[omp_get_thread_num()],
            boundr ? boundr::tell::zediv<FInterval<double>, value_type> : tell::zediv_fast<value_type>,
            ask::zediv<value_type>); break;
          case MIN: r = wrap_propagate(prop_kind, sig, Itv(xl, xu), Itv(yl, yu), Itv(zl, zu), stats_list[omp_get_thread_num()], tell::zmin<value_type>, ask::zmin<value_type>); break;
          case MAX: r = wrap_propagate(prop_kind, sig, Itv(xl, xu), Itv(yl, yu), Itv(zl, zu), stats_list[omp_get_thread_num()], tell::zmax<value_type>, ask::zmax<value_type>); break;
          case REQ: r = wrap_propagate(prop_kind, sig, Itv(xl, xu), Itv(yl, yu), Itv(zl, zu), stats_list[omp_get_thread_num()], tell::zreq<value_type>, ask::zreq<value_type>); break;
          case RLEQ: r = wrap_propagate(prop_kind, sig, Itv(xl, xu), Itv(yl, yu), Itv(zl, zu), stats_list[omp_get_thread_num()], tell::zrleq<value_type>, ask::zrleq<value_type>); break;
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

#define RANGEITV 100000

template <class Itv, class URNG>
Itv random_interval(URNG& rng, int min_v = -RANGEITV, int max_v = RANGEITV) {
  std::uniform_int_distribution<int> coin(0, 99);
  std::uniform_int_distribution<int> val(min_v, max_v);
  std::uniform_int_distribution<int> smallw(0, 8);
  std::uniform_int_distribution<int> medw(0, 100);
  std::uniform_int_distribution<int> side(0, 1);

  int mode = coin(rng);

  int l, u;

  // 20% singleton intervals.
  if(mode < 20) {
    l = u = val(rng);
  }
  // 20% small intervals.
  else if(mode < 40) {
    l = val(rng);
    u = std::min(max_v, l + smallw(rng));
  }
  // 20% medium intervals.
  else if(mode < 60) {
    l = val(rng);
    u = std::min(max_v, l + medw(rng));
  }
  // 20% intervals biased around zero.
  else if(mode < 80) {
    std::uniform_int_distribution<int> around_zero(-20, 20);
    l = around_zero(rng);
    u = around_zero(rng);
    if(l > u) std::swap(l, u);
  }
  // 20% wide intervals.
  else {
    l = val(rng);
    u = val(rng);
    if(l > u) std::swap(l, u);
  }

  return Itv(l, u);
}

template <class Itv, class URNG>
Itv random_divisor_interval(URNG& rng, int min_v = -RANGEITV, int max_v = RANGEITV) {
  std::uniform_int_distribution<int> coin(0, 99);
  std::uniform_int_distribution<int> val(min_v, max_v);
  std::uniform_int_distribution<int> pos(1, max_v);
  std::uniform_int_distribution<int> neg(min_v, -1);
  std::uniform_int_distribution<int> span(0, 50);

  int mode = coin(rng);

  int l, u;

  // 30%: interval crossing zero.
  if(mode < 30) {
    std::uniform_int_distribution<int> left(-50, 0);
    std::uniform_int_distribution<int> right(0, 50);
    l = left(rng);
    u = right(rng);
    if(l > u) std::swap(l, u);
  }
  // 20%: singleton zero.
  else if(mode < 50) {
    l = u = 0;
  }
  // 15%: strictly positive small interval.
  else if(mode < 65) {
    l = pos(rng);
    u = std::min(max_v, l + span(rng));
  }
  // 15%: strictly negative small interval.
  else if(mode < 80) {
    u = neg(rng);
    l = std::max(min_v, u - span(rng));
    if(l > u) std::swap(l, u);
  }
  // 20%: generic interval.
  else {
    l = val(rng);
    u = val(rng);
    if(l > u) std::swap(l, u);
  }

  return Itv(l, u);
}

template <class Itv>
void benchmark_random_division(const char* itv_name, bool csv, size_t samples = 1000, uint64_t seed = 0) {
  using value_type = typename Itv::value_type;

  std::vector<std::tuple<Sig, PropKind>> prop_kinds = {
    // {FDIV, P},
    // {CDIV, P},
    {TDIV, FP},
    // {EDIV, P},
    // {FDIV, DP},
    // {CDIV, DP},
    // {TDIV, DP},
    // {EDIV, DP},
    // {MUL, FP}
  };

  constexpr bool boundr = false;

  for(auto [sig, prop_kind] : prop_kinds) {
    std::vector<Statistics> stats_list(omp_get_max_threads());
    size_t not_best = 0;
    size_t total = 0;

    #pragma omp parallel
    {
      int tid = omp_get_thread_num();
      std::mt19937_64 rng(seed + 0x9e3779b97f4a7c15ULL * (tid + 1));

      size_t local_not_best = 0;
      size_t local_total = 0;

      #pragma omp for schedule(static)
      for(size_t i = 0; i < samples; ++i) {
        Itv a = random_interval<Itv>(rng);
        Itv b = random_divisor_interval<Itv>(rng); // divisor-specialized
        Itv c = random_interval<Itv>(rng);
        int r = 0;
        switch(sig) {
          case MUL:
            r = wrap_propagate(prop_kind, sig, a, b, c,
              stats_list[tid], tell::zmul<value_type>, ask::zmul<value_type>);
            break;
          case FDIV:
            r = wrap_propagate(prop_kind, sig, a, b, c,
              stats_list[tid], tell::zfdiv<value_type>, ask::zfdiv<value_type>);
            break;
          case CDIV:
            r = wrap_propagate(prop_kind, sig, a, b, c,
              stats_list[tid], tell::zcdiv<value_type>, ask::zcdiv<value_type>);
            break;
          case TDIV: r = wrap_propagate(prop_kind, sig, a, b, c, stats_list[omp_get_thread_num()],
            boundr ? boundr::tell::ztdiv<FInterval<double>, value_type> : tell::ztdiv<value_type>,
            ask::ztdiv<value_type>); break;
            break;
          case EDIV:
            r = wrap_propagate(prop_kind, sig, a, b, c,
              stats_list[tid], tell::zediv<value_type>, ask::zediv<value_type>);
            break;
          default:
            printf("ERROR!\n");
            std::exit(1);
        }

        local_not_best += r;
        local_total += 1;
      }

      #pragma omp atomic
      not_best += local_not_best;
      #pragma omp atomic
      total += local_total;
    }

    Statistics stats;
    for(size_t i = 0; i < stats_list.size(); ++i) {
      stats.merge(stats_list[i]);
    }

    if(csv) {
      printf("%s,%s,%s,%zu,%zu,%.2f,%zu,%.2f,",
        itv_name,
        sig_to_string(sig),
        prop_kind_to_string(prop_kind),
        total,
        not_best,
        100.0 * (double(not_best) / double(total)),
        total - not_best,
        100.0 * (double(total - not_best) / double(total)));
      stats.print_csv(total);
      printf("\n");
      std::cout << std::flush;
    }
    else {
      printf("%s %s (%s): ", itv_name, sig_to_string(sig), prop_kind_to_string(prop_kind));
      printf("Random interval test.\n");
      printf("Not the best on %zu examples for %zu tested (%.2f%%).\n",
        not_best, total, 100.0 * (double(not_best) / double(total)));
      printf("The best on %zu examples for %zu tested (%.2f%%).\n",
        total - not_best, total, 100.0 * (double(total - not_best) / double(total)));
      stats.print(total);
      std::cout << std::flush;
    }
  }
}

int main(int argc, char** argv) {
  bool csv = false;
  if(csv) {
    printf("abstract_domain,operation,propagator,width,total,not_best,not_best_percentage,best,best_percentage,concrete_time_ms,abstract_time_ms,bottom_propagations,bottom_propagations_percent,bottom_concrete_propagations,bottom_concrete_propagations_percent,idempotent_propagations,idempotent_propagations_percent,incomplete_ask,incomplete_ask_percent,fixpoint_iterations_dict\n");
  }
  // benchmark_random_division<ZInterval<long long>>("ZInterval<long long>", csv);
  benchmark<ZInterval<int>>("ZInterval<int>", csv);
  // benchmark<ZInterval<long long>>("ZInterval<long long>", csv);
  // benchmark<ZInterval<float>>("ZInterval<float>", csv);
  // benchmark<ZInterval<double>>("ZInterval<double>", csv);
  return 0;
}

// g++ -std=c++23 -O3 -march=native -fopenmp -I ../include/ -I ../../cuda-battery/include/ bench.cpp
