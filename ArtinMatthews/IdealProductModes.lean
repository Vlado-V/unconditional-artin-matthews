module

public import ArtinMatthews.IdealProductBasis


set_option backward.privateInPublic true
@[expose] public section

/-! Product modes identify coordinate averaging with the exact finite
Hoeffding coefficient mask on the original harmonic product measure. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators ComplexConjugate InnerProductSpace
noncomputable section
attribute [local instance] Classical.propDecidable

theorem idealHarmonicAtom_pos (P : Finset ℕ) (hV : 0 < bandReciprocalMass P)
    (hp : ∀ p∈P,0 < p) (p : ↥P) : 0 < markedHarmonicAtom P p := by
  unfold markedHarmonicAtom
  exact div_pos (one_div_pos.mpr (Nat.cast_pos.mpr (hp p p.property))) hV

theorem idealLabelMass_sqrt {J : Type*} [Fintype J]
    (P : J → Finset ℕ) {M : ℕ} (hV : ∀ j,0 < bandReciprocalMass (P j))
    (a : MarkedPhysicalMarking P M) :
    Real.sqrt (idealLabelMass P M a)=∏ j,∏ i,Real.sqrt (markedHarmonicAtom (P j) (a j i)) := by
  unfold idealLabelMass
  rw [Real.sqrt_prod _ (fun j _ => prod_nonneg fun i _ => markedHarmonicAtom_nonneg (P j) (hV j))]
  apply prod_congr rfl
  intro j _
  exact Real.sqrt_prod _ (fun i _ => markedHarmonicAtom_nonneg (P j) (hV j))

def idealCoordinateMode {α : Type*} [Fintype α] (w : α → ℝ)
    (b : OrthonormalBasis α ℂ (EuclideanSpace ℂ α)) (t a : α) : ℂ :=
  b t a/(Real.sqrt (w a):ℂ)

theorem idealCoordinateMode_constant {α : Type*} [Fintype α]
    (w : α → ℝ) (hw : ∀ a,0 < w a)
    (b : OrthonormalBasis α ℂ (EuclideanSpace ℂ α)) (a₀ : α)
    (hb : b a₀=idealProbabilityRoot w) (a : α) :
    idealCoordinateMode w b a₀ a=1 := by
  rw [idealCoordinateMode,hb]
  change (Real.sqrt (w a):ℂ)/(Real.sqrt (w a):ℂ)=1
  exact div_self (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (hw a)).ne')

theorem idealCoordinateMode_mean {α : Type*} [Fintype α]
    (w : α → ℝ) (hw : ∀ a,0 < w a)
    (b : OrthonormalBasis α ℂ (EuclideanSpace ℂ α)) (a₀ : α)
    (hb : b a₀=idealProbabilityRoot w) (t : α) :
    (∑ a,(w a:ℂ)*idealCoordinateMode w b t a)=if a₀=t then 1 else 0 := by
  have hi := (orthonormal_iff_ite.mp b.orthonormal) a₀ t
  rw [hb] at hi
  rw [idealProbabilityRoot,EuclideanSpace.inner_toLp_toLp] at hi
  change (∑ a,(b t a)*star (Real.sqrt (w a):ℂ))=_ at hi
  rw [← hi]
  apply sum_congr rfl
  intro a _
  have hs : (Real.sqrt (w a):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (hw a)).ne'
  have hs2 : (Real.sqrt (w a):ℂ)^2=(w a:ℂ) := by
    rw [← Complex.ofReal_pow,Real.sq_sqrt (hw a).le]
  simp only [idealCoordinateMode,Complex.star_def,Complex.conj_ofReal]
  rw [← hs2]
  field_simp

def idealProductMode {J : Type*} [Fintype J] {P : J → Finset ℕ} {M : ℕ}
    (b : ∀ j,OrthonormalBasis ↥(P j) ℂ (EuclideanSpace ℂ ↥(P j)))
    (t a : MarkedPhysicalMarking P M) : ℂ :=
  ∏ j,∏ i,idealCoordinateMode (markedHarmonicAtom (P j)) (b j) (t j i) (a j i)

theorem idealProductMode_eq {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) {M : ℕ} (hV : ∀ j,0 < bandReciprocalMass (P j))
    (b : ∀ j,OrthonormalBasis ↥(P j) ℂ (EuclideanSpace ℂ ↥(P j)))
    (t a : MarkedPhysicalMarking P M) :
    idealProductMode b t a=idealProductBasisVector b t a/(Real.sqrt (idealLabelMass P M a):ℂ) := by
  simp only [idealProductMode,idealCoordinateMode,prod_div_distrib,idealProductBasisVector,
    PiLp.toLp_apply,idealLabelMass_sqrt P hV,Complex.ofReal_prod]

theorem idealLabelExpectation_product {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) {M : ℕ} (f : ∀ j,Fin M → ↥(P j) → ℂ) :
    idealLabelExpectation P M (fun a => ∏ j,∏ i,f j i (a j i))=
      ∏ j,∏ i,∑ p : ↥(P j),(markedHarmonicAtom (P j) p:ℂ)*f j i p := by
  unfold idealLabelExpectation idealLabelMass
  simp only [map_prod,← prod_mul_distrib]
  exact idealTuple_sum_product (P:=P) (M:=M)
    (fun j i p => (markedHarmonicAtom (P j) p:ℂ)*f j i p)

def IdealAverageSurvives {J : Type*} {P : J → Finset ℕ} {M : ℕ}
    (a₀ : ∀ j,↥(P j)) (S : Finset (J × Fin M)) (t : MarkedPhysicalMarking P M) : Prop :=
  ∀ j i,(j,i)∈S → t j i=a₀ j

theorem idealProductMode_average {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) {M : ℕ} (hV : ∀ j,0 < bandReciprocalMass (P j))
    (hw : ∀ j p,0 < markedHarmonicAtom (P j) p)
    (b : ∀ j,OrthonormalBasis ↥(P j) ℂ (EuclideanSpace ℂ ↥(P j)))
    (a₀ : ∀ j,↥(P j)) (hb : ∀ j,b j (a₀ j)=idealProbabilityRoot (markedHarmonicAtom (P j)))
    (S : Finset (J × Fin M)) (t a : MarkedPhysicalMarking P M) :
    idealAverageSet P S (idealProductMode b t) a=
      if IdealAverageSurvives a₀ S t then idealProductMode b t a else 0 := by
  let F : ∀ j,Fin M → ↥(P j) → ℂ := fun j i p =>
    idealCoordinateMode (markedHarmonicAtom (P j)) (b j) (t j i)
      (if (j,i)∈S then p else a j i)
  have he : idealAverageSet P S (idealProductMode b t) a=
      idealLabelExpectation P M (fun z => ∏ j,∏ i,F j i (z j i)) := by
    unfold idealAverageSet idealProductMode
    apply congrArg (idealLabelExpectation P M)
    funext z
    apply prod_congr rfl
    intro j _
    apply prod_congr rfl
    intro i _
    dsimp only [F,idealMix]
    split_ifs <;> rfl
  rw [he,idealLabelExpectation_product P F]
  dsimp only [F]
  change (∏ j,∏ i,∑ p,(markedHarmonicAtom (P j) p:ℂ)*
    idealCoordinateMode (markedHarmonicAtom (P j)) (b j) (t j i)
      (if (j,i)∈S then p else a j i))=
    if IdealAverageSurvives a₀ S t then
      ∏ j,∏ i,idealCoordinateMode (markedHarmonicAtom (P j)) (b j) (t j i) (a j i) else 0
  by_cases ht : IdealAverageSurvives a₀ S t
  · rw [ite_eq_left ht]
    apply prod_congr rfl
    intro j _
    apply prod_congr rfl
    intro i _
    by_cases hS : (j,i)∈S
    · simp only [hS,ite_true]
      rw [idealCoordinateMode_mean _ (hw j) _ _ (hb j),ht j i hS]
      rw [idealCoordinateMode_constant _ (hw j) _ _ (hb j)]
      simp
    · simp only [hS,ite_false,← sum_mul]
      rw [← Complex.ofReal_sum,markedHarmonicAtom_sum _ (hV j),Complex.ofReal_one,one_mul]
  · rw [ite_eq_right ht]
    unfold IdealAverageSurvives at ht
    push Not at ht
    obtain ⟨j,i,hS,hi⟩ := ht
    apply prod_eq_zero (mem_univ j)
    apply prod_eq_zero (mem_univ i)
    simp only [hS,ite_true]
    rw [idealCoordinateMode_mean _ (hw j) _ _ (hb j),ite_eq_right (Ne.symm hi)]

end
end ArtinMatthews
