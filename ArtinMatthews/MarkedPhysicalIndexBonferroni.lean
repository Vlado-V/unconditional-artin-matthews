module

public import ArtinMatthews.MarkedPhysicalIndexMonomialTransport


set_option backward.privateInPublic true
@[expose] public section

/-! Pointwise Bonferroni truncation of the original zero-extended
physical index damping, retaining the full source guard. Its monomials
are exactly the ones passed to the selected-modulus root estimate. -/

noncomputable section
namespace ArtinMatthews
open OAI.Erdos970.NumberTheoryLean
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def MarkedPhysicalIndexSourceGuard {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x d₀ Y U V : ℝ) {n R S : ℕ}
    (i : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x) (markedPadSlots x) n R)
    (hR : 1≤R) (r : MarkedPhysicalCanonicalRoot S U (16*U) V (2*V)) : Prop :=
  MarkedPhysicalIndexRootValid i r ∧ markedPhysicalCoordinateIndexPath i.2.1 (Fin.last n)=(1,0) ∧
    markedRootNormalizedPoint U V r.2.1∈markedPhysicalCoordinateIndexGoodSet e x d₀ Y U V i hR

def markedPhysicalIndexPolynomialWeight {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x d₀ Y U V : ℝ) {n R S : ℕ}
    (i : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x) (markedPadSlots x) n R)
    (hR : 1≤R) (q : ℝ) (k : ℕ)
    (r : MarkedPhysicalCanonicalRoot S U (16*U) V (2*V)) : ℂ :=
  if MarkedPhysicalIndexSourceGuard e x d₀ Y U V i hR r then
    (markedPhysicalJointBonferroni Finset.univ i.1 (markedMemoryVisitQ q n)
      (fun v => (markedPhysicalIndexLiftedPosition i r v).1.natAbs) k:ℂ)
  else 0

def markedPhysicalIndexTailWeight {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x d₀ Y U V : ℝ) {n R S : ℕ}
    (i : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x) (markedPadSlots x) n R)
    (hR : 1≤R) (q : ℝ) (k : ℕ)
    (r : MarkedPhysicalCanonicalRoot S U (16*U) V (2*V)) : ℝ :=
  if MarkedPhysicalIndexSourceGuard e x d₀ Y U V i hR r then
    markedPhysicalJointBonferroniTail Finset.univ i.1 (markedMemoryVisitQ q n)
      (fun v => (markedPhysicalIndexLiftedPosition i r v).1.natAbs) k
  else 0

theorem markedPhysicalIndexSourceGuard_ite {α : Type*}
    {J : Type*} [Fintype J] [DecidableEq J] (e : J → ℝ) (x d₀ Y U V : ℝ) {n R S : ℕ}
    (i : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x) (markedPadSlots x) n R)
    (hR : 1≤R) (r : MarkedPhysicalCanonicalRoot S U (16*U) V (2*V)) (a b : α) :
    (if MarkedPhysicalIndexRootValid i r ∧
        markedPhysicalCoordinateIndexPath i.2.1 (Fin.last n)=(1,0) ∧
        markedRootNormalizedPoint U V r.2.1∈markedPhysicalCoordinateIndexGoodSet e x d₀ Y U V i hR then a else b) =
      if MarkedPhysicalIndexSourceGuard e x d₀ Y U V i hR r then a else b := by
  by_cases h : MarkedPhysicalIndexSourceGuard e x d₀ Y U V i hR r
  · have h' : MarkedPhysicalIndexRootValid i r ∧
        markedPhysicalCoordinateIndexPath i.2.1 (Fin.last n)=(1,0) ∧
        markedRootNormalizedPoint U V r.2.1∈markedPhysicalCoordinateIndexGoodSet e x d₀ Y U V i hR := h
    exact (ite_eq_left h').trans (ite_eq_left h).symm
  · have h' : ¬(MarkedPhysicalIndexRootValid i r ∧
        markedPhysicalCoordinateIndexPath i.2.1 (Fin.last n)=(1,0) ∧
        markedRootNormalizedPoint U V r.2.1∈markedPhysicalCoordinateIndexGoodSet e x d₀ Y U V i hR) := h
    exact (ite_eq_right h').trans (ite_eq_right h).symm

theorem markedPhysicalIndexMonomialWeight_guard
    {J : Type*} [Fintype J] [DecidableEq J] (e : J → ℝ) (x d₀ Y U V : ℝ) {n R S : ℕ}
    (i : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x) (markedPadSlots x) n R)
    (hR : 1≤R) (q : ℝ) (T : Finset ℕ)
    (r : MarkedPhysicalCanonicalRoot S U (16*U) V (2*V)) :
    markedPhysicalIndexMonomialWeight e x d₀ Y U V i hR q T r =
      if MarkedPhysicalIndexSourceGuard e x d₀ Y U V i hR r then
        (markedPhysicalJointBonferroniMonomial Finset.univ i.1 (markedMemoryVisitQ q n)
          (fun v => (markedPhysicalIndexLiftedPosition i r v).1.natAbs) T:ℂ) else 0 :=
  markedPhysicalIndexSourceGuard_ite e x d₀ Y U V i hR r _ _

theorem markedPhysicalIndexPolynomialWeight_monomials
    {J : Type*} [Fintype J] [DecidableEq J] (e : J → ℝ) (x d₀ Y U V : ℝ) {n R S : ℕ}
    (i : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x) (markedPadSlots x) n R)
    (hR : 1≤R) (q : ℝ) (k : ℕ)
    (r : MarkedPhysicalCanonicalRoot S U (16*U) V (2*V)) :
    markedPhysicalIndexPolynomialWeight e x d₀ Y U V i hR q k r =
      ∑ j ∈ Finset.range (k+1),(-1:ℂ)^j*
        ∑ T ∈ (markedPhysicalBandPrimes (fun a => markedLogPowerBand (e a) x) \ markedPhysicalPathUsedPrimes Finset.univ i.1).powersetCard j,
          markedPhysicalIndexMonomialWeight e x d₀ Y U V i hR q T r := by
  by_cases hg : MarkedPhysicalIndexSourceGuard e x d₀ Y U V i hR r
  · simp only [markedPhysicalIndexPolynomialWeight,ite_eq_left hg]
    have hm := congrArg (fun a : ℝ => (a:ℂ)) (markedPhysicalJointBonferroni_monomials
      Finset.univ i.1 (markedMemoryVisitQ q n) (fun v => (markedPhysicalIndexLiftedPosition i r v).1.natAbs) k)
    push_cast at hm
    simpa only [markedPhysicalIndexMonomialWeight_guard,ite_eq_left hg] using hm
  · simp only [markedPhysicalIndexPolynomialWeight,markedPhysicalIndexMonomialWeight_guard,
      ite_eq_right hg,Finset.sum_const_zero,mul_zero]

theorem markedPhysicalIndexTailWeight_monomials
    {J : Type*} [Fintype J] [DecidableEq J] (e : J → ℝ) (x d₀ Y U V : ℝ) {n R S : ℕ}
    (i : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x) (markedPadSlots x) n R)
    (hR : 1≤R) (q : ℝ) (k : ℕ)
    (r : MarkedPhysicalCanonicalRoot S U (16*U) V (2*V)) :
    (markedPhysicalIndexTailWeight e x d₀ Y U V i hR q k r:ℂ) =
      ∑ T ∈ (markedPhysicalBandPrimes (fun a => markedLogPowerBand (e a) x) \ markedPhysicalPathUsedPrimes Finset.univ i.1).powersetCard k,
        markedPhysicalIndexMonomialWeight e x d₀ Y U V i hR q T r := by
  by_cases hg : MarkedPhysicalIndexSourceGuard e x d₀ Y U V i hR r
  · simp only [markedPhysicalIndexTailWeight,markedPhysicalIndexMonomialWeight_guard,
      ite_eq_left hg]
    unfold markedPhysicalJointBonferroniTail BonferroniDensity.elementarySum markedPhysicalJointBonferroniMonomial
    rw [Finset.mul_sum]
    push_cast
    rfl
  · simp only [markedPhysicalIndexTailWeight,Complex.ofReal_zero,
      markedPhysicalIndexMonomialWeight_guard,ite_eq_right hg,Finset.sum_const_zero]

theorem markedPhysicalIndexDamping_bonferroni_error
    {J : Type*} [Fintype J] [DecidableEq J] (e : J → ℝ) (x d₀ Y U V : ℝ)
    (hdis : Pairwise (fun j k => Disjoint (markedLogPowerBand (e j) x) (markedLogPowerBand (e k) x)))
    {n R S : ℕ} [NeZero S] (hn : 0<n)
    (i : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x) (markedPadSlots x) n R)
    (hR : 1≤R) (hU : 1<U) (hV : 1<V)
    (r : MarkedPhysicalCanonicalRoot S U (16*U) V (2*V))
    (w : ↥(markedPhysicalPrimitiveBox U (16*U) V (2*V)) → ℤ × ℤ)
    (hw : ∀ a,markedMinorIntegerDet a.1 (w a)=1) {q : ℝ} (hq0 : 0≤q) (hq1 : q≤1) (m : ℕ) :
    ‖markedPhysicalCoordinateIndexDamping (fun j => markedLogPowerBand (e j) x)
        ⌊(Real.log x)^(1/100:ℝ)⌋₊ (markedPhysicalPrimitiveBox U (16*U) V (2*V)) q
        (MarkedPhysicalActualGood e x d₀ Y w) i r-
      markedPhysicalIndexPolynomialWeight e x d₀ Y U V i hR q (2*m) r‖ ≤
      markedPhysicalIndexTailWeight e x d₀ Y U V i hR q (2*m+1) r := by
  have hd : markedPhysicalCoordinateIndexDamping (fun j => markedLogPowerBand (e j) x)
      ⌊(Real.log x)^(1/100:ℝ)⌋₊ (markedPhysicalPrimitiveBox U (16*U) V (2*V)) q
      (MarkedPhysicalActualGood e x d₀ Y w) i r =
      if MarkedPhysicalIndexSourceGuard e x d₀ Y U V i hR r then
        (markedPhysicalJointPrimeWeight Finset.univ i.1 (markedMemoryVisitQ q n)
          (fun v => (markedPhysicalIndexLiftedPosition i r v).1.natAbs):ℂ) else 0 :=
    (markedPhysicalCoordinateIndexDamping_formula e x d₀ Y U V hn i hR hU hV r w hw hq0).trans
      (markedPhysicalIndexSourceGuard_ite e x d₀ Y U V i hR r _ _)
  rw [hd]
  by_cases hg : MarkedPhysicalIndexSourceGuard e x d₀ Y U V i hR r
  · simp only [markedPhysicalIndexPolynomialWeight,markedPhysicalIndexTailWeight,ite_eq_left hg]
    rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    exact markedPhysicalJointBonferroni_upper_error hdis Finset.univ i.1 (markedMemoryVisitQ q n)
      (fun v _ => markedPhysicalVisitQ_mem_unitInterval hq0 hq1 n v)
      (fun v => (markedPhysicalIndexLiftedPosition i r v).1.natAbs) m
  · simp only [markedPhysicalIndexPolynomialWeight,markedPhysicalIndexTailWeight,
      ite_eq_right hg,sub_self,norm_zero,le_refl]

end ArtinMatthews
