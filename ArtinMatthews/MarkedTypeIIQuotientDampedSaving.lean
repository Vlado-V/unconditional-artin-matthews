module

public import ArtinMatthews.GiantMarkedCharacterCriterion
public import ArtinMatthews.GiantMarkedSelectedDamping
public import ArtinMatthews.MarkedTypeIIDyadQuotient
public import ArtinMatthews.MarkedTypeIILabelDyads
public import ArtinMatthews.GiantMarkedSelectedSquareSource
public import ArtinMatthews.MarkedMajorTypeIICoefficients
public import ArtinMatthews.MarkedTypeIIDyadDampingJoin
public import ArtinMatthews.MarkedTypeIIDyadSummation
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! The actual occupied dyad bounds reassemble to the literal quotient
damping model. Adding the proved squareful replacement error returns the
original fixed-character centered-giant rectangle. -/

namespace ArtinMatthews
noncomputable section
open Filter Finset
open scoped BigOperators Topology

variable {J : Type*} [Fintype J]

theorem giantMarkedQuotientDampedSum_log_saving_of_determinants
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j) (heUpper : ∀ j,e j ≤ (1/5:ℝ))
    (hgroups : 2 ≤ Fintype.card J) (δ Cbox Cα Cβ G : ℝ) (hδ : 0 < δ) (hbox : 0 < Cbox) :
    ∀ᶠ x : ℝ in atTop, ∀ Hm Hn : ℝ, x^δ ≤ Hm → x^δ ≤ Hn → Hm*Hn ≤ Cbox*x →
      ∀ M N : Finset ℕ, (∀ m ∈ M, 0 < m ∧ (m:ℝ) ≤ 2*Hm) →
      (∀ n ∈ N, 0 < n ∧ (n:ℝ) ≤ 2*Hn) →
      ∀ α β F : ℕ → ℂ, (∀ m ∈ M, ‖α m‖ ≤ (Real.log x)^Cα) →
      (∀ n ∈ N, ‖β n‖ ≤ (Real.log x)^Cβ) → (∀ h, ‖F h‖ ≤ 1) →
      let P := fun j => markedLogPowerBand (e j) x
      let I := markedTypeIILabelDyadIndices (markedMajorLabelSet P)
      (∀ j ∈ I, let Y := (2:ℝ)^j
        ‖markedTypeIIDeterminantSum (markedTypeIIOccupiedLabelEndpoints P Y M N)
          (markedTypeIILabelEndpointCoefficient P Y α β)‖ ≤ Y*(Hm*Hn)*(Real.log x)^(-(2*G+5))) →
      ‖giantMarkedQuotientDampedSum P M N α β F‖ ≤ (Hm*Hn)*(Real.log x)^(-G) := by
  filter_upwards [markedTypeIISelectedLabelDyadSum_sum_log_saving_of_determinants
    e he heUpper hgroups δ Cbox Cα Cβ G hδ hbox,
    markedTypeII_actual_label_dyad_reassembly_eq_quotientDampedSum e he heUpper hgroups]
    with x hsave hjoin
  intro Hm Hn hHm hHn hX M N hM hN α β F hα hβ hF
  dsimp only
  intro hD
  exact (congrArg (fun z : ℂ => ‖z‖) (hjoin M N α β F)).symm.le.trans
    (hsave Hm Hn hHm hHn hX M N hM hN α β F hα hβ hF hD)

theorem giant_marked_character_giant_typeII_log_saving_of_determinants [DecidableEq J]
    (e : J → ℝ) (hinj : Function.Injective e)
    (he : ∀ j,(1/10:ℝ) < e j ∧ e j < (1/5:ℝ)) (hgroups : 2 ≤ Fintype.card J)
    (δ Cbox C G : ℝ) (hδ : 0 < δ) (hbox : 0 < Cbox)
    {ε : ℝ} (hε : 0 < ε) (hεq : ε < 1/4) :
    ∀ᶠ L : ℝ in atTop,
      let x := Real.exp L
      let P := fun j => markedLogPowerBand (e j) x
      let W := Real.exp (L^(6/25:ℝ))
      let F := giantMarkedCenteredCore ε x
      ∀ (q : ℕ) (χ : DirichletCharacter ℂ q)
        (Hm Hn modulation : ℝ) (M N : Finset ℕ) (β : ℕ → ℂ),
        Real.exp (δ*L) ≤ Hm → Real.exp (δ*L) ≤ Hn → Hm*Hn ≤ Cbox*x →
        (∀ m ∈ M, Hm ≤ (m:ℝ) ∧ (m:ℝ) ≤ 2*Hm) →
        (∀ n ∈ N, Hn ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*Hn) →
        (∀ n ∈ N, ‖β n‖ ≤ L^C) →
        let αχ := giantFixedCharacterReplacementCoefficient χ W modulation
        let βχ := fun n : ℕ => χ n * β n
        let I := markedTypeIILabelDyadIndices (markedMajorLabelSet P)
        (∀ j ∈ I, let Y := (2:ℝ)^j
          ‖markedTypeIIDeterminantSum (markedTypeIIOccupiedLabelEndpoints P Y M N)
            (markedTypeIILabelEndpointCoefficient P Y αχ βχ)‖ ≤ Y*(Hm*Hn)*L^(-(2*G+7))) →
        ‖∑ m ∈ M, ∑ n ∈ N, χ (m*n) * markedMajorCenteredCoefficient W modulation m *
          β n * F (m*n-1) * (literalMarkedArrayWeight e x (m*n-1):ℂ)‖ ≤ Hm*Hn*L^(-G) := by
  have hDamped := Real.tendsto_exp_atTop.eventually
    (giantMarkedQuotientDampedSum_log_saving_of_determinants e (fun j => (he j).1.le)
      (fun j => (he j).2.le) hgroups δ Cbox 2 C (G+1) hδ hbox)
  have hCore := Real.tendsto_exp_atTop.eventually
    (giantMarkedCenteredCore_interface e (fun j => (he j).2.trans (by norm_num)) hε hεq)
  filter_upwards [hDamped, hCore, markedMajorTypeII_alpha_bound δ hδ,
    giant_marked_character_giant_quotient_damping_log_saving e hinj he δ C (G+1) hδ hε hεq,
    eventually_ge_atTop (2:ℝ)] with L hdamped hcore halpha hsquareful hL
  dsimp only
  intro q χ Hm Hn modulation M N β hHm hHn hX hM hN hβ
  let x := Real.exp L
  let P := fun j => markedLogPowerBand (e j) x
  let W := Real.exp (L^(6/25:ℝ))
  let F := giantMarkedCenteredCore ε x
  let αχ := giantFixedCharacterReplacementCoefficient χ W modulation
  let βχ := fun n : ℕ => χ n * β n
  intro hD
  have hLp : 0 < L := (by norm_num : (0:ℝ) < 2).trans_le hL
  have hscale : x^δ = Real.exp (δ*L) := by
    dsimp only [x]
    rw [Real.rpow_def_of_pos (Real.exp_pos L),Real.log_exp,mul_comm L δ]
  have hMp (m : ℕ) (hm : m ∈ M) : 0 < m ∧ (m:ℝ) ≤ 2*Hm :=
    ⟨Nat.cast_pos.mp ((Real.exp_pos _).trans_le (hHm.trans (hM m hm).1)),(hM m hm).2⟩
  have hNp (n : ℕ) (hn : n ∈ N) : 0 < n ∧ (n:ℝ) ≤ 2*Hn :=
    ⟨Nat.cast_pos.mp ((Real.exp_pos _).trans_le (hHn.trans (hN n hn).1)),(hN n hn).2⟩
  have hαχ (m : ℕ) (hm : m ∈ M) : ‖αχ m‖ ≤ L^(2:ℝ) := by
    rw [Real.rpow_two]
    exact (giantFixedCharacterReplacementCoefficient_norm_le χ W modulation m).trans
      (halpha m modulation (hHm.trans (hM m hm).1))
  have hβχ (n : ℕ) (hn : n ∈ N) : ‖βχ n‖ ≤ L^C := by
    change ‖χ n*β n‖ ≤ _
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)).trans (hβ n hn)
  have hExp : 2*(G+1)+5 = 2*G+7 := by ring
  let T := giantMarkedQuotientDampedSum P M N αχ βχ F
  have hT : ‖T‖ ≤ Hm*Hn*L^(-(G+1)) := by
    have hh := hdamped Hm Hn (hscale.symm ▸ hHm) (hscale.symm ▸ hHn) hX M N hMp hNp αχ βχ F
      (fun m hm => by simpa only [Real.log_exp] using hαχ m hm)
      (fun n hn => by simpa only [Real.log_exp] using hβχ n hn) hcore.1
    simpa only [Real.log_exp] using hh (by simpa only [Real.log_exp,hExp] using hD)
  let S := ∑ m ∈ M, ∑ n ∈ N, χ (m*n) * markedMajorCenteredCoefficient W modulation m *
    β n * F (m*n-1) * (literalMarkedArrayWeight e x (m*n-1):ℂ)
  have hST : ‖S-T‖ ≤ Hm*Hn*L^(-(G+1)) :=
    hsquareful q χ Hm Hn modulation M N β hHm hHn hM hN hβ
  have hpow : L^(-(G+1)) = L^(-G)*L⁻¹ := by
    rw [show -(G+1) = (-G)+(-1) by ring,Real.rpow_add hLp,Real.rpow_neg_one]
  have htwo : 2*L⁻¹ ≤ 1 := by
    simpa only [div_eq_mul_inv] using (div_le_one hLp).mpr hL
  have hX₀ : 0 ≤ Hm*Hn := mul_nonneg ((Real.exp_pos _).le.trans hHm) ((Real.exp_pos _).le.trans hHn)
  change ‖S‖ ≤ _
  calc
    _ ≤ ‖S-T‖+‖T‖ := by simpa only [sub_add_cancel] using norm_add_le (S-T) T
    _ ≤ Hm*Hn*L^(-(G+1)) + Hm*Hn*L^(-(G+1)) := add_le_add hST hT
    _ = (Hm*Hn)*(2*L⁻¹)*L^(-G) := by rw [hpow]; ring
    _ ≤ (Hm*Hn)*1*L^(-G) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left htwo hX₀) (Real.rpow_nonneg hLp.le _)
    _ = _ := by rw [mul_one]

end
end ArtinMatthews
