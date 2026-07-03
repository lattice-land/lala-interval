// Copyright 2026 Pierre Talbot

#ifndef LALA_INTERVAL_ZF_BRIDGE_HPP
#define LALA_INTERVAL_ZF_BRIDGE_HPP

#include <iostream>
#include "battery/memory.hpp"
#include "lala/finterval.hpp"
#include "lala/zinterval.hpp"

namespace lala {

namespace tell {

  // Let `x = floor(y)` where `y` is a floating-point interval and `x` either an integer or floating-point interval.
  template<class Itv, class FT>
  CUDA INLINE constexpr void floor(Itv& x, FInterval<FT>& y) {

  }
}

namespace boundr {

// TODO: if VT is already a floating-point type, rd_cast / ru_cast are not going to behave as expected. We need floor/ceil instead.

template<class FItv, class FProp, class VT>
CUDA INLINE constexpr void ftell(FProp p, ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  using battery::rd_cast;
  using battery::ru_cast;
  using FT = typename FItv::value_type;
  FItv xf(rd_cast<FT, VT>(x.lb()), ru_cast<FT, VT>(x.ub()));
  FItv yf(rd_cast<FT, VT>(y.lb()), ru_cast<FT, VT>(y.ub()));
  FItv zf(rd_cast<FT, VT>(z.lb()), ru_cast<FT, VT>(z.ub()));
  p(xf, yf, zf);
  x.meet(ZInterval<VT>(ru_cast<VT, FT>(xf.lb()), rd_cast<VT, FT>(xf.ub())));
  y.meet(ZInterval<VT>(ru_cast<VT, FT>(yf.lb()), rd_cast<VT, FT>(yf.ub())));
  z.meet(ZInterval<VT>(ru_cast<VT, FT>(zf.lb()), rd_cast<VT, FT>(zf.ub())));
}

template<class FItv, class FAsk, class VT>
CUDA INLINE constexpr bool fask(FAsk ask, ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  using battery::rd_cast;
  using battery::ru_cast;
  using FT = typename FItv::value_type;
  FItv xf(rd_cast<FT, VT>(x.lb()), ru_cast<FT, VT>(x.ub()));
  FItv yf(rd_cast<FT, VT>(y.lb()), ru_cast<FT, VT>(y.ub()));
  FItv zf(rd_cast<FT, VT>(z.lb()), ru_cast<FT, VT>(z.ub()));
  return ask(xf, yf, zf);
}

namespace tell {

template<class FItv, class VT>
CUDA INLINE constexpr void zadd(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  ::lala::boundr::ftell<FItv>(::lala::tell::fadd<typename FItv::value_type>, x, y, z);
}

template<class FItv, class VT>
CUDA INLINE constexpr void zsub(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  ::lala::boundr::ftell<FItv>(::lala::tell::fsub<typename FItv::value_type>, x, y, z);
}

template<class FItv, class VT>
CUDA INLINE constexpr void zmul(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  ::lala::boundr::ftell<FItv>(::lala::tell::fmul<typename FItv::value_type>, x, y, z);
}

template<class FItv, class VT>
CUDA INLINE constexpr void zfdiv(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  using battery::rd_cast;
  using battery::ru_cast;
  using FT = typename FItv::value_type;
  FItv xf(rd_cast<FT, VT>(x.lb() /* - VT{1} */), ru_cast<FT, VT>(x.ub() + VT{1}));
  FItv yf(rd_cast<FT, VT>(y.lb()), ru_cast<FT, VT>(y.ub()));
  FItv zf(rd_cast<FT, VT>(z.lb()), ru_cast<FT, VT>(z.ub()));
  ::lala::tell::fdiv<typename FItv::value_type>(xf, yf, zf);
  x.meet(ZInterval<VT>(rd_cast<VT, FT>(xf.lb()), rd_cast<VT, FT>(xf.ub())));
  y.meet(ZInterval<VT>(ru_cast<VT, FT>(yf.lb()), rd_cast<VT, FT>(yf.ub())));
  z.meet(ZInterval<VT>(ru_cast<VT, FT>(zf.lb()), rd_cast<VT, FT>(zf.ub())));
}

template<class FItv, class VT>
CUDA INLINE constexpr void zcdiv(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  using battery::rd_cast;
  using battery::ru_cast;
  using FT = typename FItv::value_type;
  FItv xf(rd_cast<FT, VT>(x.lb() - VT{1}), ru_cast<FT, VT>(x.ub() /* + VT{1} */));
  FItv yf(rd_cast<FT, VT>(y.lb()), ru_cast<FT, VT>(y.ub()));
  FItv zf(rd_cast<FT, VT>(z.lb()), ru_cast<FT, VT>(z.ub()));
  ::lala::tell::fdiv<typename FItv::value_type>(xf, yf, zf);
  x.meet(ZInterval<VT>(ru_cast<VT, FT>(xf.lb()), ru_cast<VT, FT>(xf.ub())));
  y.meet(ZInterval<VT>(ru_cast<VT, FT>(yf.lb()), rd_cast<VT, FT>(yf.ub())));
  z.meet(ZInterval<VT>(ru_cast<VT, FT>(zf.lb()), rd_cast<VT, FT>(zf.ub())));
}

template<class FItv, class VT>
CUDA INLINE constexpr void ztdiv(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  using battery::rd_cast;
  using battery::ru_cast;
  using FT = typename FItv::value_type;
  FItv xf(rd_cast<FT, VT>(x.lb() > 0 ? x.lb().load() : x.lb() - VT{1}), ru_cast<FT, VT>(x.ub() < 0 ? x.ub().load() : x.ub() + VT{1}));
  FItv yf(rd_cast<FT, VT>(y.lb()), ru_cast<FT, VT>(y.ub()));
  FItv zf(rd_cast<FT, VT>(z.lb()), ru_cast<FT, VT>(z.ub()));
  ::lala::tell::fdiv<typename FItv::value_type>(xf, yf, zf);
  if(xf.ub() <= FT{0.0}) {
    x.meet(ZInterval<VT>(ru_cast<VT, FT>(xf.lb()), ru_cast<VT, FT>(xf.ub())));
  }
  else if(xf.lb() >= FT{0.0}) {
    x.meet(ZInterval<VT>(rd_cast<VT, FT>(xf.lb()), rd_cast<VT, FT>(xf.ub())));
  }
  else {
    x.meet(ZInterval<VT>(rd_cast<VT, FT>(xf.lb()), ru_cast<VT, FT>(xf.ub())));
  }
  y.meet(ZInterval<VT>(ru_cast<VT, FT>(yf.lb()), rd_cast<VT, FT>(yf.ub())));
  z.meet(ZInterval<VT>(ru_cast<VT, FT>(zf.lb()), rd_cast<VT, FT>(zf.ub())));
}

template<class FItv, class VT>
CUDA INLINE constexpr void zediv(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  using battery::rd_cast;
  using battery::ru_cast;
  using FT = typename FItv::value_type;
  FItv xf(rd_cast<FT, VT>(z.lb() >= 0 ? x.lb().load() : x.lb() - VT{1}), ru_cast<FT, VT>(z.ub() <= 0 ? x.ub().load() : x.ub() + VT{1}));
  FItv yf(rd_cast<FT, VT>(y.lb()), ru_cast<FT, VT>(y.ub()));
  FItv zf(rd_cast<FT, VT>(z.lb()), ru_cast<FT, VT>(z.ub()));
  ::lala::tell::fdiv<typename FItv::value_type>(xf, yf, zf);
  if(zf.ub() <= FT{0.0}) {
    x.meet(ZInterval<VT>(ru_cast<VT, FT>(xf.lb()), ru_cast<VT, FT>(xf.ub())));
  }
  else if(zf.lb() >= FT{0.0}) {
    x.meet(ZInterval<VT>(rd_cast<VT, FT>(xf.lb()), rd_cast<VT, FT>(xf.ub())));
  }
  else {
    x.meet(ZInterval<VT>(rd_cast<VT, FT>(xf.lb()), ru_cast<VT, FT>(xf.ub())));
  }
  y.meet(ZInterval<VT>(ru_cast<VT, FT>(yf.lb()), rd_cast<VT, FT>(yf.ub())));
  z.meet(ZInterval<VT>(ru_cast<VT, FT>(zf.lb()), rd_cast<VT, FT>(zf.ub())));
}

template<class FItv, class VT>
CUDA INLINE constexpr void zmin(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  ::lala::boundr::ftell<FItv>(::lala::tell::fmin<typename FItv::value_type>, x, y, z);
}

template<class FItv, class VT>
CUDA INLINE constexpr void zmax(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  ::lala::boundr::ftell<FItv>(::lala::tell::fmax<typename FItv::value_type>, x, y, z);
}

template<class FItv, class VT>
CUDA INLINE constexpr void zreq(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  ::lala::boundr::ftell<FItv>(::lala::tell::freq<typename FItv::value_type>, x, y, z);
}

template<class FItv, class VT>
CUDA INLINE constexpr void zrleq(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  ::lala::boundr::ftell<FItv>(::lala::tell::frleq<typename FItv::value_type>, x, y, z);
}

} // namespace tell

namespace ask {

template<class FItv, class VT>
CUDA INLINE constexpr bool zadd(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  return ::lala::boundr::fask<FItv>(::lala::ask::fadd<typename FItv::value_type>, x, y, z);
}

template<class FItv, class VT>
CUDA INLINE constexpr bool zsub(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  return ::lala::boundr::fask<FItv>(::lala::ask::fsub<typename FItv::value_type>, x, y, z);
}

template<class FItv, class VT>
CUDA INLINE constexpr bool zmul(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  return ::lala::boundr::fask<FItv>(::lala::ask::fmul<typename FItv::value_type>, x, y, z);
}

template<class FItv, class VT>
CUDA INLINE constexpr bool zmin(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  return ::lala::boundr::fask<FItv>(::lala::ask::fmin<typename FItv::value_type>, x, y, z);
}

template<class FItv, class VT>
CUDA INLINE constexpr bool zmax(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  return ::lala::boundr::fask<FItv>(::lala::ask::fmax<typename FItv::value_type>, x, y, z);
}

template<class FItv, class VT>
CUDA INLINE constexpr bool zreq(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  return ::lala::boundr::fask<FItv>(::lala::ask::freq<typename FItv::value_type>, x, y, z);
}

template<class FItv, class VT>
CUDA INLINE constexpr bool zrleq(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  return ::lala::boundr::fask<FItv>(::lala::ask::frleq<typename FItv::value_type>, x, y, z);
}

} // namespace ask
} // namespace boundr
} // namespace lala

#endif
