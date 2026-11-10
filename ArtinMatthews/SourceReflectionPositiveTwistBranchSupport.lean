module

public import ArtinMatthews.SourceReflectionPositiveTwistBranch
public import ArtinMatthews.SourceFrequencyUnitPart
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


set_option backward.privateInPublic true
@[expose] public section

/-! The finite branches partition the actual residue tuples. Each branch
factor is unchanged by a sixth power of a genuine exterior S-unit. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain AllowedGenerators SIntegerQuotient SIntegerPrincipalization
open VaryingKummerAnalytic StandardAdelic
open scoped NumberField Classical BigOperators AdeleRing

noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K)))

local notation "E" => SourcePrimeExponents K S₀
local notation "PE" => SourceExteriorPrime K S₀
local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "OS" => sourceRing K S₀
local notation "S" => sourceHilbertSet K S₀
local notation "Nf" => sourceKPFiniteAdeleUpperLift K hζ
local notation "U" => sourceReflectionPositiveTwistAdele K hζ S₀
local notation "wt" => sourceReflectionPositiveTwistWeight K hζ S₀

attribute [local instance] positiveTwistLabelFintype

def sourceReflectionPositiveTwistActiveSupport (e : E) (u : SourceReflectionPositiveTwistLabels K S₀ e) :
    Finset PE :=
  (e.support.attach.filter (fun P => u P ≠ 0)).map ⟨Subtype.val,Subtype.val_injective⟩

theorem sourceReflectionPositiveTwistActiveSupport_subset (e : E)
    (u : SourceReflectionPositiveTwistLabels K S₀ e) :
    sourceReflectionPositiveTwistActiveSupport K S₀ e u ⊆ e.support := by
  intro P hP
  obtain ⟨p,_,rfl⟩ := Finset.mem_map.mp hP
  exact p.property

theorem sourceReflectionPositiveTwistActiveSupport_mem (e : E)
    (u : SourceReflectionPositiveTwistLabels K S₀ e) (P : e.support) :
    P.val ∈ sourceReflectionPositiveTwistActiveSupport K S₀ e u ↔ u P ≠ 0 := by
  constructor
  · intro h
    obtain ⟨Q,hQ,h⟩ := Finset.mem_map.mp h
    have hQP : Q = P := Subtype.ext h
    subst Q
    exact (Finset.mem_filter.mp hQ).2
  · intro h
    exact Finset.mem_map.mpr ⟨P,Finset.mem_filter.mpr ⟨Finset.mem_attach _ _,h⟩,rfl⟩

private theorem reflection_positive_active_support_unique
    (e : E) (u : SourceReflectionPositiveTwistLabels K S₀ e)
    (active : Finset PE) (hactive : active ⊆ e.support)
    (h : ∀ P : e.support, u P ≠ 0 ↔ P.val ∈ active) :
    active = sourceReflectionPositiveTwistActiveSupport K S₀ e u := by
  ext P
  constructor
  · intro hP
    exact (sourceReflectionPositiveTwistActiveSupport_mem K S₀ e u ⟨P,hactive hP⟩).mpr
      ((h ⟨P,hactive hP⟩).mpr hP)
  · intro hP
    let Q : e.support := ⟨P,sourceReflectionPositiveTwistActiveSupport_subset K S₀ e u hP⟩
    exact (h Q).mp ((sourceReflectionPositiveTwistActiveSupport_mem K S₀ e u Q).mp hP)

theorem sourceReflectionPositiveTwistBranch_sum_powerset (e : E) (W : Gf → ℂ) (qf : Gf) :
    (∑ active ∈ e.support.powerset,
      sourceReflectionPositiveTwistBranch K hζ S₀ e active W qf) =
      sourceReflectionPositiveFiniteTwist K hζ S₀ e W qf := by
  simp only [sourceReflectionPositiveTwistBranch, sourceReflectionPositiveFiniteTwist]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  let S₁ := sourceReflectionPositiveTwistActiveSupport K S₀ e u
  have hS₁ : S₁ ∈ e.support.powerset :=
    Finset.mem_powerset.mpr (sourceReflectionPositiveTwistActiveSupport_subset K S₀ e u)
  rw [Finset.sum_eq_single_of_mem S₁ hS₁]
  · exact ite_eq_left (fun P => (sourceReflectionPositiveTwistActiveSupport_mem K S₀ e u P).symm)
  · intro active hactive hne
    apply ite_eq_right
    intro h
    exact hne (reflection_positive_active_support_unique K S₀ e u active (Finset.mem_powerset.mp hactive) h)

theorem sourceReflectionPositiveTwistBranchFactor_sixth (e : E) (active : Finset PE)
    (x : OS) (r : exteriorUnitSubgroup S) :
    sourceReflectionPositiveTwistBranchFactor K hζ S₀ e active
        (x*(sourceExteriorUnitToSourceRing K S₀ r)^6) =
      sourceReflectionPositiveTwistBranchFactor K hζ S₀ e active x := by
  let y := sourceExteriorUnitToSourceRing K S₀ r
  unfold sourceReflectionPositiveTwistBranchFactor sourceReflectionPositiveTwistBranchFactorAt
  apply Finset.prod_congr rfl
  intro P _
  dsimp only
  by_cases hP : P.val ∈ active
  · simp only [hP, ite_true]
    let T := sourceHilbertSeed K S₀
    let p : OS := sourceAllowedPrimeGenerator K hζ S₀ P.val
    let hp := sourceAllowedPrimeGenerator_ideal K hζ S₀ P.val
    let R := (𝓞 K) ⧸ P.val.val.asIdeal
    let I : Ideal OS := Ideal.span {p}
    let Q : OS →+* R :=
      (generatorResidueEquiv T P.val.val P.val.property p hp).toRingHom.comp (Ideal.Quotient.mk I)
    let χ := reflectionPrimeCharacters K hζ S₀ P.val
    let j := (sourceReflectionPositiveIndex (e P.val)).val
    let f := Q.toMonoidHom.comp (sourceExteriorUnitToSourceRing K S₀)
    let a : Rˣ :=
      ⟨f r, f r⁻¹, by rw [← map_mul, mul_inv_cancel, map_one],
        by rw [← map_mul, inv_mul_cancel, map_one]⟩
    have hunit : IsUnit (Q y) := a.isUnit
    have hχ : χ ^ (6 : ℕ) = 1 := by
      rw [← sourceJacquetActualCharacter_order K hζ S₀ P.val]
      exact pow_orderOf_eq_one _
    have hj : (χ ^ j) ^ (6 : ℕ) = 1 := by
      rw [← pow_mul, Nat.mul_comm j 6, pow_mul, hχ, one_pow]
    have hpow : (χ ^ j : MulChar R ℂ) ((Q y)^6) = 1 := by
      calc
        _ = ((χ ^ j : MulChar R ℂ) (Q y)) ^ (6 : ℕ) := map_pow _ _ _
        _ = ((χ ^ j) ^ (6 : ℕ)) (Q y) :=
          (MulChar.pow_apply' (χ ^ j) (by decide : (6 : ℕ) ≠ 0) (Q y)).symm
        _ = _ := hj ▸ MulChar.one_apply hunit
    let c := sourceReflectionTameFourierCoefficient K hζ S₀ P.val (sourceReflectionPositiveIndex (e P.val)) 0
    have hr (z : OS) : sourceJacquetReduction K P.val.val
        (sourceReflectionPositiveSIntegerAt K S₀ P.val z) = Q z :=
      sourceReflectionPositiveSIntegerAt_reduce K hζ S₀ P.val z
    calc
      _ = (χ ^ j : MulChar R ℂ) (Q (x*y^6)) - c :=
        congrArg (fun z : R => (χ ^ j : MulChar R ℂ) z - c) (hr (x*y^6))
      _ = (χ ^ j : MulChar R ℂ) (Q x) - c := by
        rw [map_mul Q, map_pow Q, map_mul, hpow, mul_one]
      _ = _ := congrArg (fun z : R => (χ ^ j : MulChar R ℂ) z - c) (hr x).symm
  · simp only [hP, ite_false]

end
end ArtinMatthews
