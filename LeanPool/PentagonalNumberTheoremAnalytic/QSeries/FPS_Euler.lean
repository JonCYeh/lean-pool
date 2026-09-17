/-
Copyright (c) 2026 Jonathan Conrad, Paula Muermann, Maryna Viazovska. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Conrad, Paula Muermann, Maryna Viazovska
-/
import LeanPool.PentagonalNumberTheoremAnalytic.QSeries.FPS

/-!
# Unit and factorisation lemmas for the formal q-Pochhammer symbol

Infrastructure for the algebraic route to Euler's second identity in the formal power series
ring. This module supplies the unit and factorisation facts that argument needs:

* `constantCoeff_qPochhammer_X`, `isUnit_qPochhammer_X`: `qPochhammer (X : R⟦X⟧) n` has constant
  coefficient `1` and is therefore a unit
* `qPochhammerInf_eq_qPochhammer_mul`, `qPochhammerInf_X_eq_qPochhammer_mul`: splitting the
  infinite symbol into a finite prefix times a tail

Euler's second identity itself is proved downstream in `FPS_Algebra.lean`, where these lemmas
are combined with the finite q-binomial theorem and a limit in the pi topology.
-/

noncomputable section

open scoped MvPowerSeries.WithPiTopology
open PowerSeries Finset

namespace QSeries.FormalPowerSeries

variable {R : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]

omit [TopologicalSpace R] [DiscreteTopology R] in
/-- The constant term of `qPochhammer X n` is 1. -/
theorem constantCoeff_qPochhammer_X (n : ℕ) :
    constantCoeff (qPochhammer (X : R⟦X⟧) n) = 1 := by
  induction n with
  | zero => simp [qPochhammer]
  | succ n ih =>
    rw [qPochhammer_succ]
    simp [map_mul, map_sub, ih]

omit [TopologicalSpace R] [DiscreteTopology R] in
/-- `qPochhammer X n` is a unit in `R⟦X⟧` (its constant term is 1). -/
theorem isUnit_qPochhammer_X (n : ℕ) : IsUnit (qPochhammer (X : R⟦X⟧) n) := by
  rw [PowerSeries.isUnit_iff_constantCoeff, constantCoeff_qPochhammer_X]
  exact isUnit_one

/-- `qPochhammerInf a = qPochhammer a n · qPochhammerInf (a · X^n)`. -/
theorem qPochhammerInf_eq_qPochhammer_mul (a : R⟦X⟧) (n : ℕ) :
    qPochhammerInf a = qPochhammer a n * qPochhammerInf (a * X ^ n) := by
  induction n with
  | zero => simp [qPochhammer]
  | succ n ih =>
    rw [ih, qPochhammer_succ, mul_assoc]
    congr 1
    rw [qPochhammerInf_eq_one_sub_mul]
    ring_nf

/-- `qPochhammerInf X = qPochhammer X n · qPochhammerInf (X * X^n)`. -/
theorem qPochhammerInf_X_eq_qPochhammer_mul (n : ℕ) :
    qPochhammerInf (X : R⟦X⟧) = qPochhammer X n * qPochhammerInf (X * X ^ n) :=
  qPochhammerInf_eq_qPochhammer_mul X n

end QSeries.FormalPowerSeries

end
