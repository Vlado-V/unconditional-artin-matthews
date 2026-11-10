module

public import ArtinMatthews.ArtinRayNormConductor
public import ArtinMatthews.VaryingKummerAnalyticRayIdealSeries
public import ArtinMatthews.ArtinAbelianGlobalEuler
public import ArtinMatthews.ArtinRayFaithfulEuler
public import ArtinMatthews.QuadraticCharacterFamily
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.Tactic.Basify
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

/-! The genuine two-character Dedekind factorization, with the primitive
ray character at its exact conductor. -/
namespace ArtinMatthews.VaryingKummerAnalytic.ArtinRay
open NumberField AbelianLocal
open scoped NumberField Classical BigOperators
noncomputable section

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
variable [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L] [IsTotallyComplex K]

theorem quadraticNormConductor_dedekind_factor
    (hd : Module.finrank K L = 2) (χ : Gal(L/K) →* ℂˣ) (hχ : Function.Injective χ)
    {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta L s =
      NumberField.dedekindZeta K s * (abelianNormConductorRayCharacter K L χ).dirichlet s := by
  let : Fintype (Gal(L/K) →* ℂˣ) := Fintype.ofFinite _
  have hc : Nat.card (Gal(L/K)) = 2 := (IsGalois.card_aut_eq_finrank K L).trans hd
  have hne : (1 : Gal(L/K) →* ℂˣ) ≠ χ := (faithfulCharacter_ne_one_of_card_two hc χ hχ).symm
  have hset : (Finset.univ : Finset (Gal(L/K) →* ℂˣ)) = {1, χ} := by
    ext φ
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact character_eq_one_or_of_card_two hc χ hχ φ
  rw [dedekindZeta_eq_prod_abelianArtinEulerProduct K L hs, hset, Finset.prod_pair hne,
    abelianArtinEulerProduct_one K L hs, ← abelianNormConductorRayCharacter_dirichlet_eq_artin χ hχ hs]

end
end ArtinMatthews.VaryingKummerAnalytic.ArtinRay
