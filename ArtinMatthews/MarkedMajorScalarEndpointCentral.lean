module

public import ArtinMatthews.MarkedMajorScalarEndpointMean
public import ArtinMatthews.MarkedMajorScalarIsolated
public import ArtinMatthews.MarkedMajorLabelSumEnergy
public import ArtinMatthews.MarkedMajorMellinLabelEnergyParameters


set_option backward.privateInPublic true
@[expose] public section

/-! Uniform central cancellation for the actual product of all selected
prime bands and the two arbitrary bounded coefficient polynomials. -/
namespace ArtinMatthews
open Filter Finset MeasureTheory
open scoped ContDiff Topology
noncomputable section

private theorem scalarLabelCentralBudget
    {L P a K F V hi θ d : ℝ} (hL : 1 ≤ L)
    (_hK : 0 ≤ K) (hF : 0 ≤ F) (hV : 0 < V) (_hhi : 0 ≤ hi) (ha : 0 ≤ a)
    (hd : 0 ≤ d) (hdK : d ≤ K*L) (hθ : |θ| ≤ 2*L^a)
    (hZ : K^2*F*V⁻¹^2*hi^2*3^4 ≤ L) :
    d^2*(F*V⁻¹^2*hi^2*(1+|θ|)^4*L^(-(P+4*a+3))) ≤ L^(-P) := by
  have hLp := zero_lt_one.trans_le hL
  have hθ' : 1+|θ| ≤ 3*L^a := by linarith [Real.one_le_rpow hL ha]
  have hp : (L^a)^4=L^(4*a) := by
    rw [mul_comm (4:ℝ),Real.rpow_mul hLp.le]
    norm_num
  have hpow : L^2*L^(4*a)*L^(-(P+4*a+3)) = L^(-P-1) := by
    rw [← Real.rpow_two,← Real.rpow_add hLp,← Real.rpow_add hLp]
    congr 1
    ring
  calc
    _ ≤ (K*L)^2*(F*V⁻¹^2*hi^2*(3*L^a)^4*L^(-(P+4*a+3))) := by gcongr
    _ = (K^2*F*V⁻¹^2*hi^2*3^4)*L^(-P-1) := by
      simp only [mul_pow,hp]
      rw [← hpow]
      ring
    _ ≤ L*L^(-P-1) := mul_le_mul_of_nonneg_right hZ (Real.rpow_nonneg hLp.le _)
    _ = L^(-P) := by
      conv_lhs => lhs; rw [← Real.rpow_one L]
      rw [← Real.rpow_add hLp,show (1:ℝ)+(-P-1)= -P by ring]

theorem markedMajorScalarEndpoint_central
    (η : ℝ → ℂ) (hη : ContDiff ℝ ∞ η) {lo hi : ℝ}
    (hlo : 0 < lo) (hhi : 0 ≤ hi) (hsupp : Function.support η ⊆ Set.Icc lo hi)
    (c C₁ δ σ a Cα Cβ P Kx v₀ : ℝ)
    (hc : 0 < c) (hC₁ : 0 < C₁) (hδ : 0 < δ) (hσ : 0 ≤ σ) (ha : 0 ≤ a)
    (hCα : 0 ≤ Cα) (hCβ : 0 ≤ Cβ) (hP : 0 ≤ P) (hv₀ : 0 < v₀) :
    ∃ R : ℝ, 0 < R ∧ ∀ᶠ L : ℝ in atTop,
      ∀ {J : Type} [Fintype J] [DecidableEq J] (P₀ : Finset ℕ) (bands : J → Finset ℕ),
        (∀ p ∈ P₀,p.Prime) → (∀ j p,p ∈ bands j → p.Prime) →
        (∀ j,Disjoint P₀ (bands j)) → Pairwise (fun i j => Disjoint (bands i) (bands j)) →
        v₀ ≤ bandReciprocalMass P₀ → (∀ j,0 < bandReciprocalMass (bands j)) →
        (∀ p ∈ P₀,c*L^(1/(10:ℝ)) ≤ Real.log p) →
        (∀ p ∈ P₀,Real.log p ≤ C₁*L^(1/(5:ℝ))) →
        ∀ (Y θ H U : ℝ) (S : Finset ℕ) (l r : ℕ) (α β : ℕ → ℂ),
          0 < Y → |θ| ≤ 2*L^a → 0 < H → Real.exp (δ*L) ≤ U →
          1 ≤ H*U → H*U ≤ Real.exp (σ*L) → H*U ≤ Kx*Real.exp L →
          (∀ m ∈ S,H ≤ (m:ℝ) ∧ (m:ℝ) ≤ 2*H) → U ≤ (l:ℝ) → (r:ℝ) ≤ 2*U →
          (∀ m ∈ S,‖α m‖ ≤ L^Cα) → (∀ n ∈ Icc l r,‖β n‖ ≤ L^Cβ) →
          (∀ t ∈ Set.Icc (-(2*(H*U)*L^(a+2))) (2*(H*U)*L^(a+2)),
            ‖markedMajorScalarPolynomial S H α t‖ ≤ L^(-R)) →
          ∀ (k : ℕ) (χ : DirichletCharacter ℂ k),
            (∫ t in Set.Icc (-(2*(H*U)*L^(a+2))) (2*(H*U)*L^(a+2)),
              ‖markedMajorScalarEndpoint (fun j : Option J => j.elim P₀ bands)
                η χ θ Y H U S (Icc l r) α β t‖^2) ≤ L^(-P) := by
  obtain ⟨F,hF,hdyad⟩ := markedMajorLabelDyad_energy_of_isolated η hη hlo hhi hsupp
  let A := a+2
  let P' := P+4*a+3
  have hA : 0 ≤ A := by dsimp only [A]; linarith
  have hP' : 0 ≤ P' := by dsimp only [P']; linarith
  obtain ⟨R,hR,hiso⟩ := markedMajorScalar_isolated_log_saving (c/2) C₁ (σ+1) δ σ (A+1) Cα Cβ P'
    (by positivity) hC₁ (by linarith) hδ hσ (by linarith) hCα hCβ hP'
  let K := 1+C₁/Real.log 2
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  let Z := K^2*F*v₀⁻¹^2*hi^2*3^4
  refine ⟨R,hR,?_⟩
  filter_upwards [hiso,markedMajorPrimeDyads_uniform c C₁ hc hC₁,
    markedMajorLabelEnergy_height_parameters A σ Kx hA,
    eventually_ge_atTop (max 1 Z)] with L hiso hdyads hheight hL
  have hL₁ : 1 ≤ L := (le_max_left _ _).trans hL
  have hLp := zero_lt_one.trans_le hL₁
  intro J _ _ P₀ bands hP₀ hbands hdis₀ hdis hV₀ hV hloP hhiP
    Y θ H U S l r α β hY hθ hH hU hX hupper hcomp hS hl hr hα hβ hlong k χ
  let T := 2*(H*U)*L^A
  obtain ⟨hT,hTlog,_,hTR⟩ := hheight (H*U) hX hupper hcomp
  let V := bandReciprocalMass P₀
  have hVp : 0 < V := hv₀.trans_le hV₀
  let M := markedMajorScalarPolynomial S H α
  let N := markedMajorScalarPolynomial (Icc l r) U β
  have hMc : Continuous M := markedMajorScalarPolynomial_continuous S H α
  have hNc : Continuous N := markedMajorScalarPolynomial_continuous (Icc l r) U β
  obtain ⟨MB,hMB⟩ := markedMajorScalarPolynomial_bounded S H α
  obtain ⟨NB,hNB⟩ := markedMajorScalarPolynomial_bounded (Icc l r) U β
  obtain ⟨hcard,hscales⟩ := hdyads P₀ hP₀ hloP hhiP
  have hpiece (j : ℕ) (hj : j ∈ markedMajorPrimeDyadIndices P₀) :
      (∫ t in Set.Icc (-T) T,‖markedMajorLabelDyad bands (markedMajorPrimeDyad P₀ j)
        η χ θ Y V t*M t*N t‖^2) ≤ F*V⁻¹^2*hi^2*(1+|θ|)^4*L^(-P') := by
    obtain ⟨hYj,hYlo,hYhi⟩ := hscales j hj
    have hprime (p : ℕ) (hp : p ∈ markedMajorPrimeDyad P₀ j) :=
      markedMajorPrimeDyad_bounds P₀ j p hP₀ hp
    have hsl (p : ℕ) (hp : p ∈ markedMajorPrimeDyad P₀ j) : ((2:ℕ)^j:ℝ) ≤ p := by
      exact_mod_cast (hprime p hp).2.1
    have hsu (p : ℕ) (hp : p ∈ markedMajorPrimeDyad P₀ j) : (p:ℝ) ≤ 2*((2:ℕ)^j:ℝ) := by
      exact_mod_cast (hprime p hp).2.2.le
    apply hdyad bands hbands hdis hV (markedMajorPrimeDyad P₀ j) (fun p hp => (hprime p hp).1)
      Y (((2:ℕ)^j:ℝ)) V θ T hY (by linarith) hVp hsl hsu χ M N hMc hNc MB NB (L^(-P')) hMB hNB
      (Real.rpow_nonneg hLp.le _)
    intro ξ
    exact hiso (((2:ℕ)^j:ℝ)) T H U S l r α β hYj hYlo hYhi hT hTlog hH hU hX hupper hTR
      hS hl hr hα hβ hlong k χ ξ (markedMajorPrimeDyad P₀ j) (fun p hp => (hprime p hp).1) hsu
  have hfinite := markedMajor_finite_sum_energy (markedMajorPrimeDyadIndices P₀)
    (fun j t => markedMajorLabelDyad bands (markedMajorPrimeDyad P₀ j) η χ θ Y V t*M t*N t)
    (fun j _ => ((markedMajorLabelDyad_continuous bands _ η χ θ Y V).mul hMc).mul hNc)
    T (F*V⁻¹^2*hi^2*(1+|θ|)^4*L^(-P')) hpiece
  have hid (t : ℝ) :
      markedMajorScalarEndpoint (fun j : Option J => j.elim P₀ bands) η χ θ Y H U S (Icc l r) α β t =
        ∑ j ∈ markedMajorPrimeDyadIndices P₀,
          markedMajorLabelDyad bands (markedMajorPrimeDyad P₀ j) η χ θ Y V t*M t*N t := by
    unfold markedMajorScalarEndpoint
    rw [markedMajorLabelPolynomial_dyad_sum P₀ bands hP₀ hbands hdis₀ hdis]
    simp only [sum_mul,V,M,N]
  simp_rw [hid]
  apply hfinite.trans
  have hVin := inv_anti₀ hv₀ hV₀
  have hfac : F*V⁻¹^2*hi^2*(1+|θ|)^4*L^(-P') ≤
      F*v₀⁻¹^2*hi^2*(1+|θ|)^4*L^(-P') := by gcongr
  exact (mul_le_mul_of_nonneg_left hfac (sq_nonneg _)).trans
    (scalarLabelCentralBudget hL₁ hK hF.le hv₀ hhi ha (Nat.cast_nonneg _) hcard hθ
      ((le_max_right _ _).trans hL))

end
end ArtinMatthews
