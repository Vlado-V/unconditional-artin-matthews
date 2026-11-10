module

public import ArtinMatthews.SourceAdelicStandardHaar
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Rational rows from the actual product adelic fundamental domain. -/
namespace ArtinMatthews
open NumberField MeasureTheory Set
open scoped NumberField AdeleRing Topology Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F]
local instance sourceAdelicBlichfeldt_measurableSpace : MeasurableSpace 𝔸[F] := borel 𝔸[F]
local instance sourceAdelicBlichfeldt_borelSpace : BorelSpace 𝔸[F] := ⟨rfl⟩
local instance sourceAdelicBlichfeldt_sFinite : SFinite (sourceKPAdelicStandardHaar F) := by
  unfold sourceKPAdelicStandardHaar
  infer_instance
local notation "L" => sourceKPAdelicRationals F
local notation "D" => sourceKPAdelicFundamentalDomain F
local notation "μ" => sourceKPAdelicStandardHaar F

def sourceKPAdelicRowDomain : Set (𝔸[F] × 𝔸[F]) := D ×ˢ D

def sourceKPAdelicRowHaar : Measure (𝔸[F] × 𝔸[F]) :=
  (sourceKPAdelicStandardHaar F).prod (sourceKPAdelicStandardHaar F)

def sourceKPAdelicRationalRows : AddSubgroup (𝔸[F] × 𝔸[F]) :=
  (sourceKPAdelicRationals F).prod (sourceKPAdelicRationals F)

instance sourceKPAdelicRationalRows_countable : Countable (sourceKPAdelicRationalRows F) := by
  let f : sourceKPAdelicRationalRows F → L × L := fun x =>
    (⟨x.val.1, x.property.1⟩, ⟨x.val.2, x.property.2⟩)
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact Prod.ext (congrArg Subtype.val (congrArg Prod.fst h))
      (congrArg Subtype.val (congrArg Prod.snd h))
  exact hf.countable

local instance sourceAdelicBlichfeldt_measurableConstVAdd : MeasurableConstVAdd (sourceKPAdelicRationalRows F) (𝔸[F] × 𝔸[F]) where
  measurable_const_vadd g := by
    change Measurable (fun x : 𝔸[F] × 𝔸[F] => (g.val.1 + x.1, g.val.2 + x.2))
    exact ((measurable_const_add g.val.1).comp measurable_fst).prodMk
      ((measurable_const_add g.val.2).comp measurable_snd)

local instance sourceAdelicBlichfeldt_vAddInvariant : VAddInvariantMeasure (sourceKPAdelicRationalRows F)
    (𝔸[F] × 𝔸[F]) (sourceKPAdelicRowHaar F) where
  measure_preimage_vadd g s hs := by
    have h := (measurePreserving_add_left (sourceKPAdelicStandardHaar F) g.val.1).prod
      (measurePreserving_add_left (sourceKPAdelicStandardHaar F) g.val.2)
    exact h.measure_preimage hs.nullMeasurableSet

theorem sourceKPAdelicRowDomain_isFundamental :
    IsAddFundamentalDomain (sourceKPAdelicRationalRows F)
      (sourceKPAdelicRowDomain F) (sourceKPAdelicRowHaar F) := by
  apply IsAddFundamentalDomain.mk'
    (((sourceKPAdelicFundamentalDomain_measurable F).prod
      (sourceKPAdelicFundamentalDomain_measurable F)).nullMeasurableSet)
  intro x
  obtain ⟨a, ha, hua⟩ := sourceKPAdelicFundamentalDomain_unique F x.1
  obtain ⟨b, hb, hub⟩ := sourceKPAdelicFundamentalDomain_unique F x.2
  refine ⟨⟨(algebraMap F 𝔸[F] (-a), algebraMap F 𝔸[F] (-b)),
    ⟨⟨-a, rfl⟩, ⟨-b, rfl⟩⟩⟩, ?_, ?_⟩
  · change (algebraMap F 𝔸[F] (-a) + x.1) ∈ D ∧
      (algebraMap F 𝔸[F] (-b) + x.2) ∈ D
    simpa only [map_neg, sub_eq_add_neg, add_comm] using And.intro ha hb
  · intro z hz
    have hzr : ∃ r : F, algebraMap F 𝔸[F] r = z.val.1 := z.property.1
    have hzs : ∃ s : F, algebraMap F 𝔸[F] s = z.val.2 := z.property.2
    obtain ⟨r, hr⟩ := hzr
    obtain ⟨s, hs⟩ := hzs
    change (z.val.1 + x.1) ∈ D ∧ (z.val.2 + x.2) ∈ D at hz
    rw [← hr, ← hs] at hz
    apply Subtype.ext
    apply Prod.ext
    · rw [← hr]
      apply congrArg (algebraMap F 𝔸[F])
      have h := hua (-r) (by simpa only [map_neg, sub_neg_eq_add, add_comm] using hz.1)
      simpa only [neg_neg] using congrArg Neg.neg h
    · rw [← hs]
      apply congrArg (algebraMap F 𝔸[F])
      have h := hub (-s) (by simpa only [map_neg, sub_neg_eq_add, add_comm] using hz.2)
      simpa only [neg_neg] using congrArg Neg.neg h

theorem sourceKPAdelicRowDomain_mass :
    sourceKPAdelicRowHaar F (sourceKPAdelicRowDomain F) = 1 := by
  unfold sourceKPAdelicRowHaar sourceKPAdelicRowDomain
  rw [Measure.prod_prod, sourceKPAdelicStandardHaar_fundamentalDomain, one_mul]

/-- Every measurable adelic row set of mass greater than one has a nonzero
rational difference. -/
theorem sourceKPAdelicRow_blichfeldt (S : Set (𝔸[F] × 𝔸[F]))
    (hS : NullMeasurableSet S (sourceKPAdelicRowHaar F))
    (hvol : 1 < sourceKPAdelicRowHaar F S) :
    ∃ q : F × F, q ≠ 0 ∧ ∃ x ∈ S, ∃ y ∈ S,
      (algebraMap F 𝔸[F] q.1, algebraMap F 𝔸[F] q.2) = y - x := by
  have hfund := sourceKPAdelicRowDomain_isFundamental F
  obtain ⟨x, hx, y, hy, g, hg, hxy⟩ := hfund.exists_ne_zero_vadd_eq hS
    (by simpa only [sourceKPAdelicRowDomain_mass] using hvol)
  have hgr : ∃ r : F, algebraMap F 𝔸[F] r = g.val.1 := g.property.1
  have hgs : ∃ s : F, algebraMap F 𝔸[F] s = g.val.2 := g.property.2
  obtain ⟨r, hr⟩ := hgr
  obtain ⟨s, hs⟩ := hgs
  have hpair : g.val = (algebraMap F 𝔸[F] r, algebraMap F 𝔸[F] s) :=
    Prod.ext hr.symm hs.symm
  refine ⟨(r, s), ?_, x, hx, y, hy, ?_⟩
  · intro hz
    apply hg
    apply Subtype.ext
    change g.val = (0 : 𝔸[F] × 𝔸[F])
    rw [hpair]
    have hr0 := congrArg Prod.fst hz
    have hs0 := congrArg Prod.snd hz
    simp only [Prod.fst_zero, Prod.snd_zero] at hr0 hs0
    simp only [hr0, hs0, map_zero, Prod.mk_zero_zero]
  · change g.val + x = y at hxy
    rw [hpair] at hxy
    change (algebraMap F 𝔸[F] r, algebraMap F 𝔸[F] s) + x = y at hxy
    exact eq_sub_iff_add_eq.mpr hxy

end
end ArtinMatthews
