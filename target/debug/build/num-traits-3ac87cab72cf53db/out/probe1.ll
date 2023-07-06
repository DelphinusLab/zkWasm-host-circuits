; ModuleID = 'probe1.dad99e3a-cgu.0'
source_filename = "probe1.dad99e3a-cgu.0"
target datalayout = "e-m:o-i64:64-i128:128-n32:64-S128"
target triple = "arm64-apple-macosx11.0.0"

; core::f64::<impl f64>::to_int_unchecked
; Function Attrs: inlinehint uwtable
define i32 @"_ZN4core3f6421_$LT$impl$u20$f64$GT$16to_int_unchecked17h1cf7809504de228bE"(double %self) unnamed_addr #0 {
start:
; call <f64 as core::convert::num::FloatToInt<i32>>::to_int_unchecked
  %0 = call i32 @"_ZN65_$LT$f64$u20$as$u20$core..convert..num..FloatToInt$LT$i32$GT$$GT$16to_int_unchecked17h7254719d888699a3E"(double %self)
  ret i32 %0
}

; <f64 as core::convert::num::FloatToInt<i32>>::to_int_unchecked
; Function Attrs: inlinehint uwtable
define internal i32 @"_ZN65_$LT$f64$u20$as$u20$core..convert..num..FloatToInt$LT$i32$GT$$GT$16to_int_unchecked17h7254719d888699a3E"(double %self) unnamed_addr #0 {
start:
  %0 = alloca i32, align 4
  %1 = fptosi double %self to i32
  store i32 %1, ptr %0, align 4
  %2 = load i32, ptr %0, align 4
  ret i32 %2
}

; probe1::probe
; Function Attrs: uwtable
define void @_ZN6probe15probe17he997d90e0353789bE() unnamed_addr #1 {
start:
; call core::f64::<impl f64>::to_int_unchecked
  %_1 = call i32 @"_ZN4core3f6421_$LT$impl$u20$f64$GT$16to_int_unchecked17h1cf7809504de228bE"(double 1.000000e+00)
  ret void
}

attributes #0 = { inlinehint uwtable "frame-pointer"="non-leaf" "target-cpu"="apple-a14" }
attributes #1 = { uwtable "frame-pointer"="non-leaf" "target-cpu"="apple-a14" }

!llvm.module.flags = !{!0}

!0 = !{i32 7, !"PIC Level", i32 2}
