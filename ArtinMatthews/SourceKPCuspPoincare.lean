module

public import ArtinMatthews.SourceKPCuspTraceHaar
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import ArtinMatthews.SourceKPCuspDirections
public import ArtinMatthews.UnitTorusPoincare
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
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
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

/-! The genuine Poincare bound on the principal finite-level cusp cover,
    expressed in directions of its actual scaled Minkowski lattice. -/

set_option relaxedAutoImplicit false

namespace ArtinMatthews
open NumberField IsDedekindDomain Module Module.Free MeasureTheory Topology
open scoped NumberField Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] (d : 𝓞 K) (hd : d ≠ 0)
local notation "E" => mixedEmbedding.mixedSpace K
local notation "I" => ChooseBasisIndex ℤ (𝓞 K)
local notation "Q" => SourceKPCuspPrincipalQuotient K d
local instance : MeasurableSpace Q := borel Q
local instance : BorelSpace Q := ⟨rfl⟩

def sourceKPCuspCoordinatePullback (f : C(Q, ℂ)) : C(UnitAddTorus I, ℂ) :=
  f.comp ⟨(sourceKPCuspPrincipalTorusHomeomorph K d hd).symm,
    (sourceKPCuspPrincipalTorusHomeomorph K d hd).symm.continuous⟩

def SourceKPCuspDirectionalDerivative
    (f : C(Q, ℂ)) (g : I → C(Q, ℂ)) : Prop :=
  ∀ (i : I) (x : E) (t : ℝ),
    HasDerivAt
      (fun u : ℝ => f (sourceKPCuspArchQuotientMap K d
        (x + u • sourceKPCuspLatticeBasis K d hd i)))
      (g i (sourceKPCuspArchQuotientMap K d
        (x + t • sourceKPCuspLatticeBasis K d hd i))) t

lemma sourceKPCuspDirectionalDerivative_coordinates
    (f : C(Q, ℂ)) (g : I → C(Q, ℂ))
    (hfg : SourceKPCuspDirectionalDerivative K d hd f g) :
    ∀ (i : I) (x : UnitAddTorus I) (t : ℝ),
      HasDerivAt
        (fun u : ℝ => f ((sourceKPCuspPrincipalTorusHomeomorph K d hd).symm
          (Function.update x i (u : UnitAddCircle))))
        (g i ((sourceKPCuspPrincipalTorusHomeomorph K d hd).symm
          (Function.update x i (t : UnitAddCircle)))) t := by
  intro i x t
  obtain ⟨y, rfl⟩ := sourceKPCuspTorusHom_surjective K d hd x
  simpa only [sourceKPCuspPrincipalTorusHomeomorph_line] using
    hfg i (y - sourceKPCuspCoordinates K d hd y i • sourceKPCuspLatticeBasis K d hd i) t

variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
include hζ

theorem sourceKPCusp_directional_poincare
    (f : C(Q, ℂ)) (g : I → C(Q, ℂ))
    (hfg : SourceKPCuspDirectionalDerivative K d hd f g)
    (hmean : (∫ x, f x ∂sourceKPCuspTraceHaar K d) = 0) :
    (2 * Real.pi) ^ 2 * (∫ x, ‖f x‖ ^ 2 ∂sourceKPCuspTraceHaar K d) ≤
      ∑ i, ∫ x, ‖g i x‖ ^ 2 ∂sourceKPCuspTraceHaar K d := by
  let e := sourceKPCuspPrincipalTorusHomeomorph K d hd
  let F : C(UnitAddTorus I, ℂ) := sourceKPCuspCoordinatePullback K d hd f
  let G : I → C(UnitAddTorus I, ℂ) := fun i => sourceKPCuspCoordinatePullback K d hd (g i)
  have he := sourceKPCuspPrincipalTorus_symm_measurePreserving K d hζ hd
  have hi (h : Q → ℂ) :
      (∫ x, h (e.symm x) ∂unitTorusHaar I) = ∫ x, h x ∂sourceKPCuspTraceHaar K d :=
    he.integral_comp e.symm.toHomeomorph.toMeasurableEquiv.measurableEmbedding h
  have hr (h : Q → ℝ) :
      (∫ x, h (e.symm x) ∂unitTorusHaar I) = ∫ x, h x ∂sourceKPCuspTraceHaar K d :=
    he.integral_comp e.symm.toHomeomorph.toMeasurableEquiv.measurableEmbedding h
  have hm : (∫ x, F x ∂unitTorusHaar I) = 0 := (hi f).trans hmean
  have hdF : ∀ (i : I) (x : UnitAddTorus I) (t : ℝ),
      HasDerivAt (fun u : ℝ => F (Function.update x i (u : UnitAddCircle)))
        (G i (Function.update x i (t : UnitAddCircle))) t :=
    sourceKPCuspDirectionalDerivative_coordinates K d hd f g hfg
  have hf : (∫ x, ‖F x‖ ^ 2 ∂unitTorusHaar I) =
      ∫ x, ‖f x‖ ^ 2 ∂sourceKPCuspTraceHaar K d := hr (fun x => ‖f x‖ ^ 2)
  have hg (i : I) : (∫ x, ‖G i x‖ ^ 2 ∂unitTorusHaar I) =
      ∫ x, ‖g i x‖ ^ 2 ∂sourceKPCuspTraceHaar K d := hr (fun x => ‖g i x‖ ^ 2)
  simpa only [hf, hg] using unitTorus_coordinate_poincare I F G hdF hm

end
end ArtinMatthews
