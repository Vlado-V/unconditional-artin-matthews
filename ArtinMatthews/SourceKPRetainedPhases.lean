module

public import ArtinMatthews.SourceKPCuspResidualFourierSymmetries
public import ArtinMatthews.SourceKPCuspResidualFourierUpper
public import ArtinMatthews.SourceKPAdelicTorusUpper
public import ArtinMatthews.SourceKPAdelicCoordinateJacquetPeriod
public import ArtinMatthews.SourceKPCuspLevelCover


set_option backward.privateInPublic true
@[expose] public section

/-! Actual finite upper roots, diagonal units, and the character of a
translated residual Fourier coefficient on the original finite cover. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain Matrix SourcePhysical StandardAdelic Filter Topology
open scoped NumberField MatrixGroups AdeleRing SourcePhysical BigOperators Classical

noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Pr" => HeightOneSpectrum (𝓞 K)
local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "Kf" => sourceKPFiniteLevelSubgroup K hζ
local notation "D" => sourceKPFiniteAdeleProjectiveDiagonalLift K hζ

def sourceKPRetainedLocalUnitHom (P : Pr) : (P.adicCompletion K)ˣ →* 𝔸ᶠ[K]ˣ :=
  (sourceKPIdeleFiniteUnit K).comp (IdeleGroup.ofAdicCompletion (𝓞 K) K P)

theorem sourceKPRetainedLocalUnitHom_apply (P : Pr) (z : (P.adicCompletion K)ˣ) :
    sourceKPRetainedLocalUnitHom K P z = sourceKPAdeleLocalUnit K P z := rfl

def sourceKPRetainedDiagonalUnit (S : Finset Pr) (z : ∀ P : S, (P.val.adicCompletion K)ˣ) :
    𝔸ᶠ[K]ˣ :=
  ∏ P : S, sourceKPAdeleLocalUnit K P.val (z P)

theorem sourceKPRetainedDiagonalUnit_at (S : Finset Pr)
    (z : ∀ P : S, (P.val.adicCompletion K)ˣ) (P : S) :
    (sourceKPRetainedDiagonalUnit K S z : 𝔸ᶠ[K]) P.val = (z P : P.val.adicCompletion K) := by
  let e := Units.map (sourceKPAdeleEval K P.val).toMonoidHom
  have he : e (sourceKPRetainedDiagonalUnit K S z) = z P := by
    rw [sourceKPRetainedDiagonalUnit, map_prod]
    calc
      _ = e (sourceKPAdeleLocalUnit K P.val (z P)) := by
        apply Finset.prod_eq_single P
        · intro Q _ hQ
          exact sourceKPAdeleLocalUnit_other K Q.val (z Q) P.val
            (fun h => hQ (Subtype.ext h.symm))
        · simp
      _ = _ := sourceKPAdeleLocalUnit_same K P.val (z P)
  exact congrArg Units.val he

section LocalPlace

variable (P : HeightOneSpectrum (𝓞 K))
local notation "L" => P.adicCompletion K
local notation "B" => sourceLocalBall K P
local notation "ψ" => localFiniteCharacter K P

def sourceKPRetainedLocalUpper (x : P.adicCompletion K) : Gf :=
  sourceKPFiniteAdeleUpperLift K hζ (sourceKPFiniteAdditiveSingle K P x)

private theorem mul_single (a : 𝔸ᶠ[K]) (x : L) :
    a * sourceKPFiniteAdditiveSingle K P x = sourceKPFiniteAdditiveSingle K P (a P*x) := by
  apply FiniteAdeleRing.ext
  intro Q
  change a Q * sourceKPFiniteAdditiveSingle K P x Q = sourceKPFiniteAdditiveSingle K P (a P*x) Q
  by_cases hQ : Q = P
  · subst Q
    rw [sourceKPFiniteAdditiveSingle_same, sourceKPFiniteAdditiveSingle_same]
  · rw [sourceKPFiniteAdditiveSingle_other K P x Q hQ,
      sourceKPFiniteAdditiveSingle_other K P (a P*x) Q hQ, mul_zero]

theorem sourceKPRetained_finiteCharacter_single (x : L) :
    finiteCharacter K (sourceKPFiniteAdditiveSingle K P x) = ψ x :=
  (localFiniteCharacter_single K P x).symm

theorem sourceKPRetainedResidual_diagonal_upper {T : ℝ} (hT : 1 ≤ T)
    (a : 𝔸ᶠ[K]ˣ) (qf : Gf) (x : L) :
    sourceKPCuspResidualFourierValue K hζ 1 hT (D a * sourceKPRetainedLocalUpper K hζ P x * qf) =
      ψ ((a:𝔸ᶠ[K]) P*x) * sourceKPCuspResidualFourierValue K hζ 1 hT (D a*qf) := by
  rw [sourceKPRetainedLocalUpper, sourceKPFiniteAdeleProjectiveDiagonalLift_upper,
    mul_single K P, mul_assoc, sourceKPCuspResidualFourierValue_left_finite_upper]
  simp only [Units.val_one, map_one, one_mul, sourceKPRetained_finiteCharacter_single]

theorem sourceKPRetained_upper_period (qf : Gf) :
    ∃ M : ℕ, 1 ≤ M ∧ ∀ x ∈ B (-(M:ℤ)),
      qf⁻¹ * sourceKPRetainedLocalUpper K hζ P x * qf ∈ Kf := by
  let e := sourceKPFiniteAdditiveSingle K P
  have hzero : e (0:L) = 0 := by
    apply add_left_cancel (a := e (0:L))
    simpa only [add_zero] using (sourceKPFiniteAdditiveSingle_add K P 0 0).symm
  have hcont : Tendsto e (𝓝 (0:L)) (𝓝 (0:𝔸ᶠ[K])) := by
    have ht := (sourceKPFiniteAdditiveSingle_continuous K P).tendsto (0:L)
    change Tendsto e (𝓝 (0:L)) (𝓝 (e 0)) at ht
    rwa [hzero] at ht
  have h := hcont.eventually (sourceKPAdelicFiniteConjugate_eventually_compact K hζ (1,qf))
  obtain ⟨n,hn⟩ := sourceLocalBall_subset_of_mem_nhds_zero K P h
  let M := max 1 (-n).toNat
  refine ⟨M,le_max_left _ _,?_⟩
  intro x hx
  have hM : -(M:ℤ) ≤ n := by
    have hle := le_max_right 1 (-n).toNat
    dsimp [M]
    omega
  have hmem : x ∈ B n := hx.trans (WithZero.exp_le_exp.mpr hM)
  have hcompact := hn hmem
  obtain ⟨k,hk⟩ := sourceKPAdelicDeepCompact_finite_lift K hζ _ hcompact (by
    change 1⁻¹ * (sourceKPAdelicUpperLift K hζ (sourceKPFiniteAddEmbedding K (e x))).1 * 1 = 1
    simp only [sourceKPAdelicUpperLift_finite_fst, inv_one, mul_one])
  exact ⟨k,(congrArg Prod.snd hk).symm⟩

theorem sourceKPRetained_phase_trivial_of_coefficient_ne_zero
    {T : ℝ} (hT : 1 ≤ T) (a : 𝔸ᶠ[K]ˣ) (qf : Gf) (M : ℕ)
    (hperiod : ∀ x ∈ B (-(M:ℤ)), qf⁻¹ * sourceKPRetainedLocalUpper K hζ P x * qf ∈ Kf)
    (hne : sourceKPCuspResidualFourierValue K hζ 1 hT (D a*qf) ≠ 0) :
    ∀ x ∈ B (-(M:ℤ)), ψ (((a:𝔸ᶠ[K]) P-1)*x) = 1 := by
  intro x hx
  let N := sourceKPRetainedLocalUpper K hζ P x
  let C := sourceKPCuspResidualFourierValue K hζ 1 hT
  have hfix : C (D a * N * qf) = C (D a*qf) := calc
    _ = C ((D a*qf)*(qf⁻¹*N*qf)) := congrArg C (by group)
    _ = _ := sourceKPCuspResidualFourierValue_right_level K hζ 1 hT (D a*qf) _ (hperiod x hx)
  have hEq : ψ ((a:𝔸ᶠ[K]) P*x) * C (D a*qf) = C (D a*qf) :=
    (sourceKPRetainedResidual_diagonal_upper K hζ P hT a qf x).symm.trans hfix
  have hψ : ψ ((a:𝔸ᶠ[K]) P*x) = 1 :=
    mul_right_cancel₀ hne (hEq.trans (one_mul _).symm)
  have hv : sourceLocalValuation K P x ≤ 1 := hx.trans (by
    rw [← WithZero.exp_zero]
    exact WithZero.exp_le_exp.mpr (by omega))
  have hneg : ψ (-x) = 1 := by
    apply localFiniteCharacter_integral K P
    apply (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K P).mpr
    change sourceLocalValuation K P (-x) ≤ 1
    rw [Valuation.map_neg]
    exact hv
  rw [show (((a:𝔸ᶠ[K]) P-1)*x) = (a:𝔸ᶠ[K]) P*x + -x by ring,
    AddChar.map_add_eq_mul, hψ, hneg, one_mul]

end LocalPlace
end
end ArtinMatthews
