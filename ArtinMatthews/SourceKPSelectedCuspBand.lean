module

public import ArtinMatthews.SourceKPAutomorphicParametricContinuity
public import ArtinMatthews.SourceKPCompactHeight
public import ArtinMatthews.SourceKPArchHaar
public import ArtinMatthews.SourceKPAutomorphicL2
public import ArtinMatthews.SourceKPAutomorphicCompactHaar
public import ArtinMatthews.SourceKPHighCuspQuotient
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

/-! A band in one actual rational Borel orbit of the finite-level fiber. -/

namespace ArtinMatthews
open NumberField Matrix Topology MulOpposite MeasureTheory
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Xf" => SourceKPFiniteLevelSpace K hζ
local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "HF" => sourceKPFiniteLevelHeight K hζ
local notation "HC" => sourceKPAdelicCoverHeight K hζ
local notation "HY" => sourceKPAutomorphicCompactOrbitHeight K hζ
local notation "μY" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)

theorem sourceKPFiniteLevelToCompact_isOpenMap :
    IsOpenMap (sourceKPFiniteLevelToCompact K hζ) :=
  (sourceKPFiniteLevelToCompact_isOpenQuotientMap K hζ).isOpenMap

theorem sourceKPFiniteLevelToCompact_height_of_high (x : Xf) (hx : 1 < HF x) :
    HY (sourceKPFiniteLevelToCompact K hζ x) = HF x := by
  change sourceKPAutomorphicOrbitHeight K hζ (Quotient.mk _ x) = HF x
  rw [sourceKPAutomorphicOrbitHeight_of_finite]
  exact sourceKPFiniteLevelOrbitHeight_eq_height_of_high K hζ x hx

def sourceKPSelectedCuspBand (b : SourceKPFiniteLevelFiber K hζ) (A B : ℝ) : Set Y :=
  sourceKPFiniteLevelToCompact K hζ ''
    {x : Xf | A < HF x ∧ HF x < B ∧
      x.2 ∈ Set.range (fun γ : sourceKPRationalBorel K => γ.val • b)}

theorem sourceKPSelectedCuspBand_isOpen (b : SourceKPFiniteLevelFiber K hζ) (A B : ℝ) :
    IsOpen (sourceKPSelectedCuspBand K hζ b A B) := by
  apply sourceKPFiniteLevelToCompact_isOpenMap K hζ
  exact (isOpen_lt continuous_const (sourceKPFiniteLevelHeight_continuous K hζ)).inter
    ((isOpen_lt (sourceKPFiniteLevelHeight_continuous K hζ) continuous_const).inter
      ((isOpen_discrete (Set.range (fun γ : sourceKPRationalBorel K => γ.val • b))).preimage
        (continuous_snd : Continuous (Prod.snd : Xf → SourceKPFiniteLevelFiber K hζ))))

theorem sourceKPSelectedCuspBand_height (b : SourceKPFiniteLevelFiber K hζ) {A B : ℝ}
    (hA : 1 ≤ A) {x : Y} (hx : x ∈ sourceKPSelectedCuspBand K hζ b A B) :
    A < HY x ∧ HY x < B := by
  obtain ⟨g,hg,rfl⟩ := hx
  rw [sourceKPFiniteLevelToCompact_height_of_high K hζ g (hA.trans_lt hg.1)]
  exact ⟨hg.1,hg.2.1⟩

theorem sourceKPSelectedCuspBand_measure_ne_top (b : SourceKPFiniteLevelFiber K hζ) {A B : ℝ}
    (hA : 1 ≤ A) : μY (sourceKPSelectedCuspBand K hζ b A B) ≠ ⊤ := by
  let : IsFiniteMeasureOnCompacts μY :=
    sourceKPAutomorphicCompactHaar_finiteOnCompacts K hζ
  apply ne_of_lt
  exact (measure_mono (fun x hx => (sourceKPSelectedCuspBand_height K hζ b hA hx).2.le)).trans_lt
    ((sourceKPAutomorphicCompactOrbitHeight_sublevel_isCompact K hζ B).measure_lt_top)

theorem sourceKPSelectedCuspBand_mem_iff (b : SourceKPFiniteLevelFiber K hζ) {A B : ℝ}
    (hA : 1 ≤ A) (q : SourceKPAdelicProjective K hζ) (hq : 1 < HC q) :
    sourceKPFiniteLevelToCompact K hζ (sourceKPFiniteLevelMk K hζ q) ∈
      sourceKPSelectedCuspBand K hζ b A B ↔
        A < HC q ∧ HC q < B ∧
          (sourceKPFiniteLevelMk K hζ q).2 ∈
            Set.range (fun γ : sourceKPRationalBorel K => γ.val • b) := by
  constructor
  · rintro ⟨x,hx,he⟩
    have he' : sourceKPAutomorphicCompactMk K hζ (Quotient.mk _ x) =
        sourceKPAutomorphicCompactMk K hζ (sourceKPAutomorphicLevelMk K hζ q) := he
    obtain ⟨k,hk⟩ := MulAction.mem_orbit_iff.mp (Quotient.exact he')
    change k.val • sourceKPAutomorphicLevelMk K hζ q = Quotient.mk _ x at hk
    rw [sourceKPAutomorphicLevelMk_archRight] at hk
    let q' : SourceKPAdelicProjective K hζ := (q.1 * unop k.val,q.2)
    change sourceKPAutomorphicLevelMk K hζ q' = Quotient.mk _ x at hk
    obtain ⟨γ,hγ⟩ := MulAction.mem_orbit_iff.mp (Quotient.exact hk.symm)
    have hqeq : HF (sourceKPFiniteLevelMk K hζ q') = HC q := by
      rw [sourceKPFiniteLevelHeight_mk]
      have hr := sourceKPAdelicCoverHeight_right_deep K hζ q
        ⟨(unop k.val,1),sourceKPArchCompactRight_deep K hζ k⟩
      have heq : q * ((unop k.val,1) : SourceKPAdelicProjective K hζ) = q' :=
        Prod.ext rfl (mul_one _)
      exact (congrArg HC heq).symm.trans hr
    have hγB : γ ∈ sourceKPRationalBorel K := by
      apply sourceKPFiniteLevelHeight_high_overlap K hζ γ (sourceKPFiniteLevelMk K hζ q')
      · rwa [hqeq]
      · rw [hγ]
        exact hA.trans_lt hx.1
    have hh : HF x = HC q :=
      (congrArg HF hγ).symm.trans
        ((sourceKPFiniteLevelHeight_rationalBorel K hζ γ hγB _).trans hqeq)
    obtain ⟨δ,hδ⟩ := hx.2.2
    change δ.val • b = x.2 at hδ
    have hf : γ • (sourceKPFiniteLevelMk K hζ q).2 = x.2 :=
      congrArg Prod.snd hγ
    refine ⟨hh ▸ hx.1,hh ▸ hx.2.1,⟨⟨γ,hγB⟩⁻¹*δ,?_⟩⟩
    change (γ⁻¹ * δ.val) • b = (sourceKPFiniteLevelMk K hζ q).2
    rw [mul_smul,hδ,← hf,inv_smul_smul]
  · intro h
    refine ⟨sourceKPFiniteLevelMk K hζ q,?_,rfl⟩
    change A < HF (sourceKPFiniteLevelMk K hζ q) ∧
      HF (sourceKPFiniteLevelMk K hζ q) < B ∧ _
    simpa only [sourceKPFiniteLevelHeight_mk] using h

end
end ArtinMatthews
