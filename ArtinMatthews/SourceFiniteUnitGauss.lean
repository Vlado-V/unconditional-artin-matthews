module

public import ArtinMatthews.SIntegerFiniteSourceFourier
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

/-! Multiplication by a source unit permutes each literal quotient.
The finite Gauss action follows by reindexing that quotient. -/
namespace ArtinMatthews.SIntegerFourier

open NumberField IsDedekindDomain SIntegerPrincipalization SIntegerQuotient StandardAdelic
open scoped NumberField Classical
noncomputable section

def sourceQuotientMulUnit {R : Type*} [CommRing R] (I : Ideal R) (u : Rˣ) : R ⧸ I ≃ R ⧸ I :=
  let v := Units.map (Ideal.Quotient.mk I).toMonoidHom u
  { toFun := fun x => (v : R ⧸ I) * x
    invFun := fun x => ((v⁻¹ : (R ⧸ I)ˣ) : R ⧸ I) * x
    left_inv := fun x => by
      change ((v⁻¹ : (R ⧸ I)ˣ) : R ⧸ I) * ((v : R ⧸ I) * x) = x
      rw [← mul_assoc, v.inv_mul, one_mul]
    right_inv := fun x => by
      change (v : R ⧸ I) * (((v⁻¹ : (R ⧸ I)ˣ) : R ⧸ I) * x) = x
      rw [← mul_assoc, v.mul_inv, one_mul] }

theorem sourceQuotientMulUnit_apply {R : Type*} [CommRing R] (I : Ideal R) (u : Rˣ) (x : R ⧸ I) :
    sourceQuotientMulUnit I u x = Ideal.Quotient.mk I (u : R) * x := rfl

theorem sourceQuotientMulUnit_mk {R : Type*} [CommRing R] (I : Ideal R) (u : Rˣ) (x : R) :
    sourceQuotientMulUnit I u (Ideal.Quotient.mk I x) = Ideal.Quotient.mk I (x * (u : R)) := by
  rw [sourceQuotientMulUnit_apply, map_mul, mul_comm]

variable {K : Type} [Field K] [NumberField K]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
local notation "OS" => PrincipalIntegerRing S₀

theorem sourceResidueGauss_eq_of_mk_eq (s : OS) (hs : s ≠ 0)
    (f : OS ⧸ Ideal.span {s} → ℂ) {x y : OS}
    (he : Ideal.Quotient.mk (Ideal.span {s}) x = Ideal.Quotient.mk (Ideal.span {s}) y) :
    sourceResidueGauss S₀ s hs f x = sourceResidueGauss S₀ s hs f y := by
  unfold sourceResidueGauss
  simp only [he]

theorem sourceResidueGauss_mul_unit (s : OS) (hs : s ≠ 0) (f : OS ⧸ Ideal.span {s} → ℂ)
    (u : OSˣ) (hf : ∀ x, f (sourceQuotientMulUnit (Ideal.span {s}) u x) = f x) (m : OS) :
    sourceResidueGauss S₀ s hs f (m * (u : OS)) = sourceResidueGauss S₀ s hs f m := by
  unfold sourceResidueGauss
  refine (tsum_congr (fun x => ?_)).trans ((sourceQuotientMulUnit (Ideal.span {s}) u).tsum_eq _)
  rw [hf, sourceQuotientMulUnit_apply, map_mul (Ideal.Quotient.mk (Ideal.span {s})), mul_assoc]

end
end ArtinMatthews.SIntegerFourier
