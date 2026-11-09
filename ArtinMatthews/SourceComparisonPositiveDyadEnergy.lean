module

public import ArtinMatthews.SourceComparisonNormalizedCutBox
public import ArtinMatthews.SourceComparisonDyadGeometry
public import ArtinMatthews.SourceComparisonHighGeometry


set_option backward.privateInPublic true
@[expose] public section

/-! The positive giant term on an actual occupied comparison dyad. -/

namespace ArtinMatthews

open Finset Filter MeasureTheory
open scoped Topology ContDiff

noncomputable section

def sourceComparisonProductCoefficient {q : ℕ} [NeZero q] (h : ZMod q)
    (β : ℕ → ℂ) (v : ℕ × ℕ × ℕ) : ℂ :=
  β v.2.2*ZMod.stdAddChar (h*(sourceComparisonTriplePosition v:ZMod q))

theorem sourceComparisonProductCoefficient_norm {q : ℕ} [NeZero q] (h : ZMod q)
    (β : ℕ → ℂ) (v : ℕ × ℕ × ℕ) :
    ‖sourceComparisonProductCoefficient h β v‖ = ‖β v.2.2‖ := by
  simp only [sourceComparisonProductCoefficient, norm_mul, giant_stdAddChar_norm, mul_one]

theorem sourceComparisonPositiveDyad_high_energy
    (ψ : ℝ → ℂ) {a b : ℝ} (ha : 0 < a)
    (hsupp : Function.support ψ ⊆ Set.Icc a b) (hψ : ContDiff ℝ ∞ ψ)
    (ε C D Q A : ℝ) (hε : 0 < ε) (hεq : ε < 1/4)
    (hD : 0 ≤ D) (hQ : 0 ≤ Q) (hA : 0 ≤ A) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (Y H σ : ℝ), Real.exp X ≤ Y → Y ≤ Real.exp ((1+ε/4)*X) →
        Real.exp (X^(38/100:ℝ)) ≤ H → H ≤ Real.exp (X/2) → |σ| ≤ X^C →
        ∀ (S : Finset ℕ) (β : ℕ → ℂ),
          (∀ p ∈ S, p.Prime ∧ Real.exp (X^(28/100:ℝ)) ≤ (p:ℝ) ∧
            (p:ℝ) ≤ Real.exp (X^(36/100:ℝ))) →
          (∀ n ∈ Ioc 0 ⌊b*Y⌋₊, ‖β n‖ ≤ X^D) →
          ∀ (q : ℕ) [NeZero q] (h : ZMod q), (q:ℝ) ≤ X^Q →
            ∀ j ∈ sourceComparisonOccupiedDyads S (giantPrimeWindow (Real.exp X) ε)
              (Ioc 0 ⌊b*Y⌋₊) a b Y,
              (∫ t in sourceComparisonHighTimes (X*Y/H) (X^B),
                ‖sourceComparisonCutTriple
                  (sourceComparisonProductBox S (giantPrimeWindow (Real.exp X) ε)
                    (Ioc 0 ⌊b*Y⌋₊) j)
                  (sourceComparisonProductCoefficient h β) ψ Y Y (t+σ)‖^2) ≤ X^(-A) := by
  obtain ⟨B,hB,henergy⟩ := sourceComparisonTupleBox_high_energy (1/2) 1 3 (ε/8) Q
    (1-ε/2) (1-2*ε) D (A+3) (by norm_num) (by norm_num) (by norm_num) (by positivity)
    hQ (by linarith) (by linarith) hD (by linarith)
  refine ⟨max (max 1 C) B+1, by linarith [le_max_right (max 1 C) B], ?_⟩
  filter_upwards [henergy, sourceComparisonNormalizedCutBox_high_energy ψ ha hsupp hψ D C B A hD hA,
    sourceComparisonSmallDyad_scales, sourceComparisonGiantDyad_scales ε Q hε hεq,
    sourceComparisonHighGeometry_window a b ε C ha hε hεq, eventually_ge_atTop (1:ℝ)]
    with X henergy hcut hsmall hgiant hgeometry hX
  intro Y H σ hY hYcap hH hHcap hσ S β hS hβ q _ h hq j hj
  let G := giantPrimeWindow (Real.exp X) ε
  let N := ⌊b*Y⌋₊
  let R := Ioc 0 N
  let P : ℝ := sourceComparisonDyadScale j.1
  let L : ℝ := sourceComparisonDyadScale j.2.1
  let U : ℝ := sourceComparisonDyadScale j.2.2
  let Z := sourceComparisonProductScale j
  let T := X*Y/H
  let u := max L ((Real.exp X)^(1-ε))
  let v := min (2*L) ((Real.exp X)^(1-ε/2))
  let l := sourceComparisonDyadScale j.2.2+1
  let r := min N (2*sourceComparisonDyadScale j.2.2)
  let S₁ := sourceComparisonDyad S j.1
  let E := sourceComparisonProductBox S G R j
  have hJ : j ∈ sourceComparisonProductDyads S G R := (mem_filter.mp hj).1
  obtain ⟨hjs,hjg,hjr⟩ := mem_product.mp hJ |>.imp_right mem_product.mp
  obtain ⟨hP,hPlo,hPhi,hPcap⟩ := hsmall S j.1 hS hjs
  obtain ⟨hjg₀,hLlo,hLu,huv,hvL,hvcap,hLcap,hunit⟩ := hgiant j.2.1 hjg
  obtain ⟨hT,hT1,hTcap,hTLU,hZcap,hUlo⟩ := hgeometry Y H P L U hY hYcap hH hHcap
    hP.le hPcap (sourceComparisonDyadScale_one_le _) hLcap (sourceComparisonDyadScale_one_le _)
    (mem_filter.mp hj).2.1 (mem_filter.mp hj).2.2
  have hX0 : 0 < X := by linarith
  have hY0 : 0 < Y := (Real.exp_pos _).trans_le hY
  have hT0 : 0 < T := (Real.rpow_pos_of_pos hX0 _).trans_le hT
  have hUmin : Real.exp ((ε/8)*X) ≤ U :=
    (Real.exp_le_exp.mpr (by nlinarith)).trans hUlo
  have hjr₀ : 0 < j.2.2 := by
    by_contra hn
    have hz : j.2.2 = 0 := by omega
    have hU1 : U = 1 := by simp [U, sourceComparisonDyadScale, hz]
    have hexp : 1 < Real.exp ((ε/4)*X) := Real.one_lt_exp_iff.mpr (by positivity)
    linarith
  have hZ1 : 1 ≤ Z := by
    have hL : 1 ≤ L := sourceComparisonDyadScale_one_le _
    have hU : 1 ≤ U := sourceComparisonDyadScale_one_le _
    change 1 ≤ P*L*U
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hP.le hL) hU
  have hLUZ : L*U ≤ Z := by
    change L*U ≤ P*L*U
    have hh := mul_le_mul_of_nonneg_right hP.le (show 0 ≤ L*U by positivity)
    nlinarith only [hh]
  have hg (m : ℕ) (hm : m ∈ G) : m.Prime :=
    ((mem_giantPrimeWindow (Real.exp_pos X).le).mp hm).1
  have hE : E = S₁×ˢ(((Ioc ⌊u⌋₊ ⌊v⌋₊).filter Nat.Prime)×ˢIcc l r) := by
    unfold E sourceComparisonProductBox
    rw [sourceComparisonGiantDyad_eq (Real.exp_pos X).le _ hjg₀,
      sourceComparisonCofactorDyad_eq N _ hjr₀]
  have hβr : ∀ n ∈ Icc l r, ‖β n‖ ≤ X^D := by
    intro n hn
    rw [← sourceComparisonCofactorDyad_eq N _ hjr₀] at hn
    exact hβ n (mem_filter.mp hn).1
  have huL : U ≤ (l:ℝ) := by dsimp [U,l]; push_cast; linarith
  have hrU : (r:ℝ) ≤ 2*U := by dsimp [U,r]; exact_mod_cast min_le_right _ _
  have hScap : ∀ p ∈ S₁, (p:ℝ) ≤ 2*P := by
    intro p hp
    have hh := (sourceComparisonDyad_bounds hp (hS p (mem_filter.mp hp).1).1.pos).2
    dsimp [P]
    exact_mod_cast hh
  have he := henergy P (2*T) L u v U l r β hP hPlo (by simpa only [one_mul] using hPhi) hT1 hTcap hLlo hLu huv hvL hvcap
    hUmin huL hrU hTLU (hLUZ.trans hZcap) hβr q h hq (hunit q hq) S₁
    (fun p hp => (hS p (mem_filter.mp hp).1).1) hScap
  have huncut (t : ℝ) :
      sourceComparisonCutTriple E (sourceComparisonProductCoefficient h β) (fun _ => 1) Z Y t =
        sourceComparisonTupleBox h S₁ ((Ioc ⌊u⌋₊ ⌊v⌋₊).filter Nat.Prime) (Icc l r) β P L U t := by
    simp only [hE, sourceComparisonCutTriple, sourceComparisonTupleBox,
      sourceComparisonProductCoefficient, sourceComparisonTriplePosition, sum_product, mul_one]
    rfl
  have hc : ∀ w ∈ E, ‖sourceComparisonProductCoefficient h β w‖ ≤ X^D := by
    intro w hw
    rw [sourceComparisonProductCoefficient_norm]
    exact hβ _ (mem_filter.mp (mem_product.mp (mem_product.mp hw).2).2).1
  exact hcut E (sourceComparisonProductCoefficient h β) Z Y T σ hZ1 hY0 (mem_filter.mp hj).2.2
    hT ((by linarith : T ≤ 2*T).trans (hTLU.trans hLUZ)) hZcap hσ
    (fun _ hw => sourceComparisonProductBox_positions_mem S G R j
      (fun p hp => (hS p hp).1.pos) (fun m hm => (hg m hm).pos)
      (fun n hn => (mem_Ioc.mp hn).1) hw) hc (by simpa only [huncut] using he)

end
end ArtinMatthews
