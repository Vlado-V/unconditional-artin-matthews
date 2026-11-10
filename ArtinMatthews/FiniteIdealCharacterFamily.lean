module

public import ArtinMatthews.KummerPrimitiveConductorFamily
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
public import Mathlib.RingTheory.Radical.NatInt
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

/-! Exact regrouping of a finite dependent ideal-character family.
The filter may depend on the actual conductor, as zero conditions do. -/
namespace ArtinMatthews
open VaryingKummerAnalytic
open OAI.SevenEighths.FiniteFourier
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
variable {K : Type} [Field K] [NumberField K]
variable {ι : Type*} [Fintype ι]

theorem finiteFamilyImageAt_dependent_filter_card_sum
    {L C : Type*} [DecidableEq L] [DecidableEq C]
    (label : ι → L) (value : ι → C) (hinj : Function.Injective value)
    (P : L → C → Prop) :
    (∑ m ∈ Finset.univ.image label, ((finiteFamilyImageAt label value m).filter (P m)).card) =
      (Finset.univ.filter (fun i => P (label i) (value i))).card := by
  calc
    _ = ∑ m ∈ Finset.univ.image label,
        (Finset.univ.filter (fun i => P (label i) (value i) ∧ label i=m)).card := by
      apply Finset.sum_congr rfl
      intro m _
      rw [finiteFamilyImageAt_filter_card label value hinj m (P m)]
      congr 1
      ext i
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      constructor
      · rintro ⟨hm,hP⟩
        exact ⟨by simpa only [hm] using hP,hm⟩
      · rintro ⟨hP,hm⟩
        exact ⟨hm,by simpa only [hm] using hP⟩
    _ = _ := by
      have h := Finset.card_eq_sum_card_fiberwise (f := label)
        (s := Finset.univ.filter (fun i => P (label i) (value i)))
        (t := Finset.univ.image label)
        (fun i _ => Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
      simpa only [Finset.filter_filter] using h.symm

def finiteIdealConductorSupport (f : ι → IdealConductorModulus K) :
    Finset (IdealConductorModulus K) := Finset.univ.image f

def finiteIdealIndicesAt (f : ι → IdealConductorModulus K) (M : IdealConductorModulus K) :
    Finset ι := Finset.univ.filter (fun i => f i=M)

omit [NumberField K] in
theorem mem_finiteIdealIndicesAt (f : ι → IdealConductorModulus K)
    (M : IdealConductorModulus K) (i : ι) : i ∈ finiteIdealIndicesAt f M ↔ f i=M := by
  simp only [finiteIdealIndicesAt,Finset.mem_filter,Finset.mem_univ,true_and]

def finiteIdealCharactersAt (f : ι → IdealConductorModulus K)
    (χ : ∀ i, EvenIdealRayCharacter K (f i).val) (M : IdealConductorModulus K) :
    Finset (EvenIdealRayCharacter K M.val) :=
  (finiteIdealIndicesAt f M).attach.image (fun i =>
    transportIdealRayCharacter ((mem_finiteIdealIndicesAt f M i.1).mp i.2) (χ i.1))

theorem mem_finiteIdealCharactersAt (f : ι → IdealConductorModulus K)
    (χ : ∀ i, EvenIdealRayCharacter K (f i).val) (M : IdealConductorModulus K)
    (ψ : EvenIdealRayCharacter K M.val) :
    ψ ∈ finiteIdealCharactersAt f χ M ↔
      ∃ i h, transportIdealRayCharacter (h : f i=M) (χ i)=ψ := by
  constructor
  · intro hψ
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hψ
    exact ⟨i.1,(mem_finiteIdealIndicesAt f M i.1).mp i.2,rfl⟩
  · rintro ⟨i,h,rfl⟩
    let j : {i : ι // i ∈ finiteIdealIndicesAt f M} :=
      ⟨i,(mem_finiteIdealIndicesAt f M i).mpr h⟩
    exact Finset.mem_image.mpr ⟨j,Finset.mem_attach _ j,rfl⟩

theorem finiteIdealCharactersAt_primitive (f : ι → IdealConductorModulus K)
    (χ : ∀ i, EvenIdealRayCharacter K (f i).val) (hχ : ∀ i, IsPrimitiveOnIdeals (χ i).residue)
    (M : IdealConductorModulus K) (ψ : EvenIdealRayCharacter K M.val)
    (hψ : ψ ∈ finiteIdealCharactersAt f χ M) : IsPrimitiveOnIdeals ψ.residue := by
  obtain ⟨i,h,rfl⟩ := (mem_finiteIdealCharactersAt f χ M ψ).mp hψ
  exact transportIdealRayCharacter_primitive h _ (hχ i)

theorem finiteIdealCharactersAt_nonprincipal (f : ι → IdealConductorModulus K)
    (χ : ∀ i, EvenIdealRayCharacter K (f i).val) (hχ : ∀ i, (χ i).IsNonprincipal)
    (M : IdealConductorModulus K) (ψ : EvenIdealRayCharacter K M.val)
    (hψ : ψ ∈ finiteIdealCharactersAt f χ M) : ψ.IsNonprincipal := by
  obtain ⟨i,h,rfl⟩ := (mem_finiteIdealCharactersAt f χ M ψ).mp hψ
  exact transportIdealRayCharacter_nonprincipal h _ (hχ i)

theorem finiteIdealConductorSupport_norm_le (f : ι → IdealConductorModulus K)
    (U : ℝ) (hf : ∀ i, ((f i).val.absNorm : ℝ) ≤ U)
    (M : IdealConductorModulus K) (hM : M ∈ finiteIdealConductorSupport f) :
    (M.val.absNorm : ℝ) ≤ U := by
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hM
  exact hf i

theorem finiteIdealCharactersAt_coefficient_image (f : ι → IdealConductorModulus K)
    (χ : ∀ i, EvenIdealRayCharacter K (f i).val) (M : IdealConductorModulus K) :
    (finiteIdealCharactersAt f χ M).image (fun ψ => ψ.coefficient) =
      finiteFamilyImageAt f (fun i => (χ i).coefficient) M := by
  ext c
  constructor
  · intro hc
    obtain ⟨ψ,hψ,rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨i,h,rfl⟩ := (mem_finiteIdealCharactersAt f χ M ψ).mp hψ
    exact (mem_finiteFamilyImageAt _ _ M _).mpr
      ⟨i,h,(transportIdealRayCharacter_coefficient h _).symm⟩
  · intro hc
    obtain ⟨i,h,he⟩ := (mem_finiteFamilyImageAt _ _ M c).mp hc
    refine Finset.mem_image.mpr ⟨transportIdealRayCharacter h (χ i),?_,?_⟩
    · exact (mem_finiteIdealCharactersAt f χ M _).mpr ⟨i,h,rfl⟩
    · exact (transportIdealRayCharacter_coefficient h _).trans he

theorem finiteIdealCharactersAt_dependent_filter_card_sum
    (f : ι → IdealConductorModulus K) (χ : ∀ i, EvenIdealRayCharacter K (f i).val)
    (hinj : Function.Injective (fun i => (χ i).coefficient))
    (P : IdealConductorModulus K → (integralFractionalIdeals K → ℂ) → Prop) :
    (∑ M ∈ finiteIdealConductorSupport f,
      (((finiteIdealCharactersAt f χ M).image (fun ψ => ψ.coefficient)).filter (P M)).card) =
      (Finset.univ.filter (fun i => P (f i) (χ i).coefficient)).card := by
  calc
    _ = ∑ M ∈ finiteIdealConductorSupport f,
        ((finiteFamilyImageAt f (fun i => (χ i).coefficient) M).filter (P M)).card := by
      apply Finset.sum_congr rfl
      intro M _
      rw [finiteIdealCharactersAt_coefficient_image]
    _ = _ := finiteFamilyImageAt_dependent_filter_card_sum f _ hinj P

end
end ArtinMatthews
