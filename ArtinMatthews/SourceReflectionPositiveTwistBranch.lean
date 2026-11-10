module

public import ArtinMatthews.SourceReflectionPositiveFiniteTwist
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! In each branch, the same finite translations are selected by their
nonzero residue support. An active place loses precisely the zero
term of its local Fourier inversion. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic StandardAdelic QuadraticWeil
open scoped NumberField Classical BigOperators AdeleRing

noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K)))

local notation "E" => SourcePrimeExponents K S₀
local notation "PE" => SourceExteriorPrime K S₀
local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "Nf" => sourceKPFiniteAdeleUpperLift K hζ
local notation "C" => sourceReflectionTameFourierCoefficient K hζ S₀
local notation "X" => sourceReflectionPositiveLocalTranslation K hζ S₀
local notation "U" => sourceReflectionPositiveTwistAdele K hζ S₀
local notation "wt" => sourceReflectionPositiveTwistWeight K hζ S₀
local notation "I[" P "]" => sourceJacquetIntegers K (Subtype.val P)
local notation "R[" P "]" => (𝓞 K) ⧸ HeightOneSpectrum.asIdeal (Subtype.val P)

attribute [local instance] positiveTwistResidueFintype positiveTwistLabelFintype

theorem sourceReflectionPositiveLocalFourier_branch
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)
    (P : PE) (j : Fin 6) (x : I[P]) (active : Prop) [Decidable active] :
    (∑ a : R[P], if a ≠ 0 ↔ active then
      C P j a * localFiniteCharacter K P.val ((x : P.val.adicCompletion K)*X P a) else 0) =
      if active then (reflectionPrimeCharacters K hζ S₀ P ^ j.val : MulChar R[P] ℂ)
        (sourceJacquetReduction K P.val x) - C P j 0 else C P j 0 := by
  let f (a : R[P]) := C P j a * localFiniteCharacter K P.val ((x : P.val.adicCompletion K)*X P a)
  have hf : f 0 = C P j 0 := by
    simp only [f, sourceReflectionPositiveLocalTranslation_zero, mul_zero,
      AddChar.map_zero_eq_one, mul_one]
  by_cases ha : active
  · simp only [ha, iff_true, ite_true]
    have h (a : R[P]) : (if a ≠ 0 then f a else 0) =
        f a - (if a = 0 then f 0 else 0) := by
      by_cases hz : a = 0 <;> simp [hz]
    change (∑ a : R[P], if a ≠ 0 then f a else 0) = _
    simp_rw [h]
    simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true, hf]
    exact congrArg (fun v : ℂ => v - C P j 0) (sourceReflectionPositiveLocalFourier K hζ S₀ P hS j x)
  · simp only [ha, iff_false, not_ne_iff, ite_false]
    change (∑ a : R[P], if a = 0 then f a else 0) = _
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, hf]

def sourceReflectionPositiveTwistBranch (e : E) (active : Finset PE) (W : Gf → ℂ) (qf : Gf) : ℂ :=
  ∑ u : SourceReflectionPositiveTwistLabels K S₀ e,
    if ∀ P : e.support, u P ≠ 0 ↔ P.val ∈ active then
      wt e u * W (Nf (U e u)*qf)
    else 0

def sourceReflectionPositiveTwistBranchFactorAt (e : E) (active : Finset PE)
    (x : (P : e.support) → I[P.val]) : ℂ :=
  ∏ P : e.support,
    let j := sourceReflectionPositiveIndex (e P.val)
    if P.val ∈ active then
      (reflectionPrimeCharacters K hζ S₀ P.val ^ j.val : MulChar R[P.val] ℂ)
        (sourceJacquetReduction K P.val.val (x P)) - C P.val j 0
    else C P.val j 0

def sourceReflectionPositiveTwistBranchFactor (e : E) (active : Finset PE) (x : sourceRing K S₀) : ℂ :=
  sourceReflectionPositiveTwistBranchFactorAt K hζ S₀ e active
    (fun P => sourceReflectionPositiveSIntegerAt K S₀ P.val x)

theorem sourceReflectionPositiveTwistBranch_eq_product
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀) (e : E) (active : Finset PE)
    (m : Kˣ) (x : (P : e.support) → I[P.val])
    (hx : ∀ P : e.support, (x P : P.val.val.adicCompletion K) =
      (sourceKPTraceJacquetFrequencyAt K P.val.val m : P.val.val.adicCompletion K))
    (W : Gf → ℂ) (qf : Gf)
    (hW : ∀ u : 𝔸ᶠ[K], W (Nf u*qf) =
      finiteCharacter K (algebraMap K 𝔸ᶠ[K] (m:K)*u)*W qf) :
    sourceReflectionPositiveTwistBranch K hζ S₀ e active W qf =
      sourceReflectionPositiveTwistBranchFactorAt K hζ S₀ e active x * W qf := by
  let f (P : e.support) (a : R[P.val]) :=
    C P.val (sourceReflectionPositiveIndex (e P.val)) a *
      localFiniteCharacter K P.val.val ((x P : P.val.val.adicCompletion K)*X P.val a)
  let g (P : e.support) (a : R[P.val]) := if a ≠ 0 ↔ P.val ∈ active then f P a else 0
  have h (u : SourceReflectionPositiveTwistLabels K S₀ e) :
      (if ∀ P : e.support, u P ≠ 0 ↔ P.val ∈ active then
        wt e u * W (Nf (U e u)*qf) else 0) =
      (∏ P : e.support, g P (u P))*W qf := by
    by_cases hu : ∀ P : e.support, u P ≠ 0 ↔ P.val ∈ active
    · rw [ite_eq_left hu, hW, sourceReflectionPositiveTwistAdele_character K hζ S₀ e m x hx,
        ← mul_assoc, sourceReflectionPositiveTwistWeight, ← Finset.prod_mul_distrib]
      apply congrArg (fun a : ℂ => a * W qf)
      apply Finset.prod_congr rfl
      intro P _
      exact (ite_eq_left (hu P)).symm
    · obtain ⟨P,hP⟩ := not_forall.mp hu
      have hz : g P (u P) = 0 := ite_eq_right hP
      rw [ite_eq_right hu, Finset.prod_eq_zero (Finset.mem_univ P) hz, zero_mul]
  unfold sourceReflectionPositiveTwistBranch
  simp_rw [h]
  rw [← Finset.sum_mul, ← Fintype.prod_sum g]
  apply congrArg (fun a : ℂ => a * W qf)
  apply Finset.prod_congr rfl
  intro P _
  exact sourceReflectionPositiveLocalFourier_branch K hζ S₀ hS P.val
    (sourceReflectionPositiveIndex (e P.val)) (x P) (P.val ∈ active)

theorem sourceReflectionPositiveTwistBranch_eq
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀) (e : E) (active : Finset PE)
    (m : Kˣ) (x : sourceRing K S₀) (hx : (m:K) = (x:K)) (W : Gf → ℂ) (qf : Gf)
    (hW : ∀ u : 𝔸ᶠ[K], W (Nf u*qf) =
      finiteCharacter K (algebraMap K 𝔸ᶠ[K] (m:K)*u)*W qf) :
    sourceReflectionPositiveTwistBranch K hζ S₀ e active W qf =
      sourceReflectionPositiveTwistBranchFactor K hζ S₀ e active x * W qf := by
  apply sourceReflectionPositiveTwistBranch_eq_product K hζ S₀ hS e active m
    (fun P => sourceReflectionPositiveSIntegerAt K S₀ P.val x) _ W qf hW
  intro P
  change algebraMap K (P.val.val.adicCompletion K) (x:K) = algebraMap K _ (m:K)
  rw [hx]

end
end ArtinMatthews
