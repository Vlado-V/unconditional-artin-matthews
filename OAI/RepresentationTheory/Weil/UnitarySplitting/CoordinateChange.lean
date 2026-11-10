module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

/-! # Coordinate Change -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.CoordinateChange.Construction

noncomputable section

/-! Continuous additive coordinate changes on the actual Bruhat space. -/

theorem schwartzBruhat_comp_addEquiv
    {F : Type} [NormedField F] {m n : ℕ}
    (e : Local.FunctionsMetaplectic.Construction.Position F m ≃ₜ+ Local.FunctionsMetaplectic.Construction.Position F n)
    {f : Local.FunctionsMetaplectic.Construction.Position F n → ℂ} (hf : f ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat F n) :
    f ∘ e ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat F m := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      rcases hf with hf | ⟨d, a, φ, rfl⟩
      · exact Local.FunctionsMetaplectic.Construction.compact_locallyConstant_mem
          (hf.1.comp_continuous e.continuous) (hf.2.comp_homeomorph e.toHomeomorph)
      · exact Local.FunctionsMetaplectic.Construction.schwartz_coordinate_mem (a.trans e.symm) φ
  | zero => exact (Local.FunctionsMetaplectic.Construction.schwartzBruhat F m).zero_mem
  | add f g _ _ hf hg => exact (Local.FunctionsMetaplectic.Construction.schwartzBruhat F m).add_mem hf hg
  | smul c f _ hf => exact (Local.FunctionsMetaplectic.Construction.schwartzBruhat F m).smul_mem c hf

def schwartzBruhat_coordinateEquiv
    {F : Type} [NormedField F] {m n : ℕ}
    (e : Local.FunctionsMetaplectic.Construction.Position F m ≃ₜ+ Local.FunctionsMetaplectic.Construction.Position F n) :
    Local.FunctionsMetaplectic.Construction.schwartzBruhat F n ≃ₗ[ℂ] Local.FunctionsMetaplectic.Construction.schwartzBruhat F m where
  toFun f := ⟨f.val ∘ e, schwartzBruhat_comp_addEquiv e f.property⟩
  invFun f := ⟨f.val ∘ e.symm, schwartzBruhat_comp_addEquiv e.symm f.property⟩
  left_inv f := by ext x; simp
  right_inv f := by ext x; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.CoordinateChange.Construction
