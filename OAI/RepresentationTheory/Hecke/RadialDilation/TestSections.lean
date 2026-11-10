module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.LocallyConstant.Basic
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

/-! # Test Sections -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.TestSections.Realization

noncomputable section

/-! Sections of locally constant compactly supported functions on products. -/

open scoped Classical _root_.Topology
open Filter

def lcCompactSpace (X : Type*) [TopologicalSpace X] : Submodule ℂ (X → ℂ) where
  carrier := {f | IsLocallyConstant f ∧ HasCompactSupport f}
  zero_mem' := ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩
  add_mem' hf hg := ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  smul_mem' c _f hf := ⟨hf.1.comp (fun z : ℂ => c * z), hf.2.smul_left⟩

theorem locallyConstant_compact_range_finite
    {X Y : Type*} [TopologicalSpace X] [Zero Y]
    (f : X → Y) (hf : IsLocallyConstant f) (hc : HasCompactSupport f) :
    (Set.range f).Finite := by
  let K := tsupport f
  let : CompactSpace K := isCompact_iff_compactSpace.mp hc
  have hK : (Set.range (fun x : K => f x.val)).Finite :=
    (hf.comp_continuous continuous_subtype_val).range_finite
  apply (hK.insert 0).subset
  rintro y ⟨x, rfl⟩
  by_cases hx : f x = 0
  · exact Set.mem_insert_iff.mpr (Or.inl hx)
  · exact Set.mem_insert_iff.mpr (Or.inr ⟨⟨x, subset_tsupport f hx⟩, rfl⟩)

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] [T2Space Y]

omit [T2Space X] [T2Space Y] in
theorem section_zero_of_not_mem_projection (f : lcCompactSpace (X × Y))
    (x : X) (hx : x ∉ Prod.fst '' tsupport f.val) (y : Y) : f.val (x, y) = 0 := by
  by_contra hn
  exact hx ⟨(x, y), subset_tsupport f.val hn, rfl⟩

def testSection (y : Y) : lcCompactSpace (X × Y) →ₗ[ℂ] lcCompactSpace X where
  toFun f := ⟨fun x => f.val (x, y),
    ⟨f.property.1.comp_continuous (continuous_id.prodMk continuous_const), by
      apply HasCompactSupport.intro (f.property.2.image continuous_fst)
      intro x hx
      exact section_zero_of_not_mem_projection f x hx y⟩⟩
  map_add' f g := rfl
  map_smul' c f := rfl

omit [T2Space Y] in
theorem testSection_locallyConstant (f : lcCompactSpace (X × Y)) :
    IsLocallyConstant (fun y => testSection y f) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro y
  have hK : IsCompact (Prod.fst '' tsupport f.val) := f.property.2.image continuous_fst
  have hnear : ∀ᶠ y' in 𝓝 y, ∀ x ∈ Prod.fst '' tsupport f.val,
      f.val (x, y') = f.val (x, y) := by
    apply hK.eventually_forall_of_forall_eventually
    intro x _
    have h₁ := (f.property.1.comp_continuous
      (continuous_snd.prodMk continuous_fst : Continuous (fun p : Y × X => (p.2, p.1)))).eventually_eq (y, x)
    have h₂ := (f.property.1.comp_continuous
      (continuous_snd.prodMk continuous_const : Continuous (fun p : Y × X => (p.2, y)))).eventually_eq (y, x)
    filter_upwards [h₁, h₂] with p hp₁ hp₂
    exact hp₁.trans hp₂.symm
  filter_upwards [hnear] with y' hy'
  apply Subtype.ext
  funext x
  by_cases hx : x ∈ Prod.fst '' tsupport f.val
  · exact hy' x hx
  · exact (section_zero_of_not_mem_projection f x hx y').trans
      (section_zero_of_not_mem_projection f x hx y).symm

theorem testSection_compactSupport (f : lcCompactSpace (X × Y)) :
    HasCompactSupport (fun y => testSection y f) := by
  apply HasCompactSupport.intro (f.property.2.image continuous_snd)
  intro y hy
  apply Subtype.ext
  funext x
  change f.val (x, y) = 0
  by_contra hn
  exact hy ⟨(x, y), subset_tsupport f.val hn, rfl⟩

theorem testSection_range_finite (f : lcCompactSpace (X × Y)) :
    (Set.range (fun y => testSection y f)).Finite :=
  locallyConstant_compact_range_finite _ (testSection_locallyConstant f) (testSection_compactSupport f)

end

end OAI.RepresentationTheory.Hecke.RadialDilation.TestSections.Realization
