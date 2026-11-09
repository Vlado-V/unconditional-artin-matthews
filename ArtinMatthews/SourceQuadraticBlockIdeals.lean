module

public import ArtinMatthews.SourceQuadraticBlockCharacter
public import ArtinMatthews.QuadraticHeckeSquarefreeNorm


set_option backward.privateInPublic true
@[expose] public section

/-! The B3 row variable is reindexed through the actual exterior-ideal
factorization. The parity cutoff becomes the norm of the unique
squarefree ideal part, with both fixed-S and common-g masks retained. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain VaryingKummerAnalytic SIntegerPrincipalization
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
local notation "E" => SourcePrimeExponents F S₀
local notation "J₀" => {J : Ideal (𝓞 F) // J ≠ ⊥}
local notation "I" => sourcePrimeExponentIdeal F S₀
local notation "q" => sourcePrimeExponentNorm F S₀

def sourceQuadraticBlockBadIdeal : Ideal (𝓞 F) :=
  Ideal.span {principalizingDenominator (sourceHilbertSeed F S₀)}

theorem sourceQuadraticBlock_exterior_coprime (d : E) :
    IsCoprime (I d) (sourceQuadraticBlockBadIdeal F S₀) :=
  (sourcePrimeExponentIdeal_exterior F S₀ d).2

theorem sourceQuadraticBlock_ideal_coprime_iff (d g : E) :
    IsCoprime (I d) (I g) ↔ Disjoint d.support g.support := by
  rw [Ideal.isCoprime_iff_sup_eq, ← sourceQuadraticExteriorIdeal_inf]
  rw [← Ideal.one_eq_top, ← sourcePrimeExponentIdeal_zero F S₀]
  rw [(sourcePrimeExponentIdeal_injective F S₀).eq_iff]
  rw [← Finsupp.disjoint_iff, disjoint_iff, bot_eq_zero]

def sourceQuadraticBlockExteriorEquiv :
    E ≃ {J : J₀ // IsCoprime J.val (sourceQuadraticBlockBadIdeal F S₀)} where
  toFun d := ⟨⟨I d, sourcePrimeExponentIdeal_ne_bot F S₀ d⟩,
    sourceQuadraticBlock_exterior_coprime F S₀ d⟩
  invFun J := sourceExteriorIdealExponents F S₀ ⟨J.val.val, J.val.property, J.property⟩
  left_inv d := by
    apply sourcePrimeExponentIdeal_injective F S₀
    exact sourceExteriorIdealExponents_recover F S₀ _
  right_inv J := by
    apply Subtype.ext
    apply Subtype.ext
    exact sourceExteriorIdealExponents_recover F S₀ _

/-- Exact exterior reindexing for an arbitrary coefficient, including its
fixed-S coprimality condition. -/
theorem sourceQuadraticBlock_tsum_exterior (f : J₀ → ℂ) :
    (∑' d : E, f ⟨I d, sourcePrimeExponentIdeal_ne_bot F S₀ d⟩) =
      ∑' J : J₀, if IsCoprime J.val (sourceQuadraticBlockBadIdeal F S₀) then f J else 0 := by
  let h : J₀ → ℂ := fun J => if IsCoprime J.val (sourceQuadraticBlockBadIdeal F S₀) then f J else 0
  have hs : Function.support h ⊆ {J : J₀ | IsCoprime J.val (sourceQuadraticBlockBadIdeal F S₀)} := by
    intro J hJ
    by_contra hn
    exact hJ (ite_eq_right hn)
  have hh := tsum_subtype_eq_of_support_subset hs
  change (∑' x : {J : J₀ // IsCoprime J.val (sourceQuadraticBlockBadIdeal F S₀)}, h x.val) =
    ∑' J : J₀, h J at hh
  rw [← (sourceQuadraticBlockExteriorEquiv F S₀).tsum_eq] at hh
  change (∑' d : E, h ⟨I d, sourcePrimeExponentIdeal_ne_bot F S₀ d⟩) =
    ∑' J : J₀, h J at hh
  simpa only [h, sourceQuadraticBlock_exterior_coprime, ite_true] using hh

theorem sourceQuadraticBlock_squarefreeNorm (d : E) :
    quadraticHeckeSquarefreeNorm F ⟨I d, sourcePrimeExponentIdeal_ne_bot F S₀ d⟩ =
      q (sourceReflectionParity d) := by
  have hfull : sourceFullIdealExponents F (I d) =
      d.embDomain (sourceReflectionExteriorPrimeEmbedding F S₀) := by
    have h := (sourceFullExponentIdealEquiv F).left_inv
      (d.embDomain (sourceReflectionExteriorPrimeEmbedding F S₀))
    change sourceFullIdealExponents F (sourceFullExponentIdeal F
      (d.embDomain (sourceReflectionExteriorPrimeEmbedding F S₀))) = _ at h
    rw [sourceReflectionFullExteriorIdeal F S₀ d] at h
    exact h
  change Ideal.absNorm (sourceFullExponentIdeal F
    (sourceReflectionParity (sourceFullIdealExponents F (I d)))) = _
  rw [hfull]
  unfold sourceReflectionParity
  rw [← Finsupp.embDomain_mapRange]
  rw [sourceReflectionFullExteriorIdeal, sourcePrimeExponentIdeal_norm]

variable [IsTotallyComplex F] {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "χ" => sourceReflectionQuadraticSymbol F S₀ hζ

/-- The exact ideal-norm tail attached to the residual column character. -/
def sourceQuadraticBlockIdealTail (M K : ℝ) (g e : E) : ℂ :=
  ∑' J : J₀, if IsCoprime J.val (sourceQuadraticBlockBadIdeal F S₀) ∧
      IsCoprime J.val (I g) ∧ K < (quadraticHeckeSquarefreeNorm F J : ℝ) then
    (sourceQuadraticRayCharacter F S₀ hζ e).allCoefficient J.val *
      (sourceQuadraticB2Bump ((Ideal.absNorm J.val : ℝ)/M) : ℂ) else 0

/-- General coefficient transport through the genuine exterior-ideal bijection. -/
theorem sourceQuadraticBlock_character_tsum (M : ℝ) (g e : E)
    (he : sourceReflectionIsSquarefree e) (P : J₀ → Prop) :
    (∑' d : E, if Disjoint d.support g.support ∧
        P ⟨I d, sourcePrimeExponentIdeal_ne_bot F S₀ d⟩ then
      (sourceQuadraticB2RowWeight F S₀ M d : ℂ)*χ d e else 0) =
      ∑' J : J₀, if IsCoprime J.val (sourceQuadraticBlockBadIdeal F S₀) ∧
          IsCoprime J.val (I g) ∧ P J then
        (sourceQuadraticRayCharacter F S₀ hζ e).allCoefficient J.val *
          (sourceQuadraticB2Bump ((Ideal.absNorm J.val : ℝ)/M) : ℂ) else 0 := by
  have hi := sourceQuadraticBlock_tsum_exterior F S₀
    (fun J => if IsCoprime J.val (I g) ∧ P J then
      (sourceQuadraticRayCharacter F S₀ hζ e).allCoefficient J.val *
        (sourceQuadraticB2Bump ((Ideal.absNorm J.val : ℝ)/M) : ℂ) else 0)
  simp only [ite_and] at hi ⊢
  rw [← hi]
  apply tsum_congr
  intro d
  rw [sourceQuadraticBlock_ideal_coprime_iff,
    sourceQuadraticRayCharacter_allCoefficient F S₀ hζ e he d, sourcePrimeExponentIdeal_norm]
  dsimp only [sourceQuadraticB2RowWeight]
  split_ifs <;> ring

theorem sourceQuadraticBlockRowKernel_eq_idealTail {M K : ℝ} (hM : 0 < M)
    (g e : E) (he : sourceReflectionIsSquarefree e) :
    sourceQuadraticBlockRowKernel F S₀ hζ (sourceQuadraticB2Rows F S₀ M K)
        (sourceQuadraticB2RowWeight F S₀ M) g e =
      sourceQuadraticBlockIdealTail F S₀ hζ M K g e := by
  have hrow := sourceQuadraticB2Rows_sum_eq_tsum F S₀ (K := K) hM
    (fun d => if Disjoint d.support g.support then χ d e else 0)
  have hi := sourceQuadraticBlock_character_tsum F S₀ hζ M g e he
    (fun J => K < (quadraticHeckeSquarefreeNorm F J : ℝ))
  unfold sourceQuadraticBlockIdealTail
  rw [← hi]
  rw [show sourceQuadraticBlockRowKernel F S₀ hζ (sourceQuadraticB2Rows F S₀ M K)
      (sourceQuadraticB2RowWeight F S₀ M) g e =
      ∑ d ∈ sourceQuadraticB2Rows F S₀ M K,
        (sourceQuadraticB2RowWeight F S₀ M d : ℂ)*
          (if Disjoint d.support g.support then χ d e else 0) by
    simp only [sourceQuadraticBlockRowKernel, mul_ite, mul_zero]]
  rw [hrow]
  apply tsum_congr
  intro d
  rw [sourceQuadraticBlock_squarefreeNorm]
  by_cases hp : K < (q (sourceReflectionParity d) : ℝ) <;>
    by_cases hd : Disjoint d.support g.support <;> simp [hp, hd]

/-- The complete source character norm sum, with its actual fixed-S and
common-g coprimality masks. -/
def sourceQuadraticBlockIdealFull (M : ℝ) (g e : E) : ℂ :=
  ∑' J : J₀, if IsCoprime J.val (sourceQuadraticBlockBadIdeal F S₀) ∧
      IsCoprime J.val (I g) then
    (sourceQuadraticRayCharacter F S₀ hζ e).allCoefficient J.val *
      (sourceQuadraticB2Bump ((Ideal.absNorm J.val : ℝ)/M) : ℂ) else 0

/-- The exact small-squarefree-part term removed by the original row cutoff. -/
def sourceQuadraticBlockIdealSmall (M K : ℝ) (g e : E) : ℂ :=
  ∑' J : J₀, if IsCoprime J.val (sourceQuadraticBlockBadIdeal F S₀) ∧
      IsCoprime J.val (I g) ∧ (quadraticHeckeSquarefreeNorm F J : ℝ) ≤ K then
    (sourceQuadraticRayCharacter F S₀ hζ e).allCoefficient J.val *
      (sourceQuadraticB2Bump ((Ideal.absNorm J.val : ℝ)/M) : ℂ) else 0

theorem sourceQuadraticBlockIdealTail_eq_full_sub_small {M K : ℝ} (hM : 0 < M)
    (g e : E) (he : sourceReflectionIsSquarefree e) :
    sourceQuadraticBlockIdealTail F S₀ hζ M K g e =
      sourceQuadraticBlockIdealFull F S₀ hζ M g e -
        sourceQuadraticBlockIdealSmall F S₀ hζ M K g e := by
  rw [← sourceQuadraticBlockRowKernel_eq_idealTail F S₀ hζ hM g e he,
    sourceQuadraticBlockRowKernel_eq_full_sub_small F S₀ hζ hM g e]
  have hfull := sourceQuadraticBlock_character_tsum F S₀ hζ M g e he (fun _ => True)
  have hsmall := sourceQuadraticBlock_character_tsum F S₀ hζ M g e he
    (fun J => (quadraticHeckeSquarefreeNorm F J : ℝ) ≤ K)
  simp only [and_true] at hfull
  simp only [sourceQuadraticBlock_squarefreeNorm] at hsmall
  rw [hfull, hsmall]
  rfl

/-- Compact support gives the absolute ideal sum required for the exact
squarefree-times-square reindexing. -/
theorem sourceQuadraticBlockIdeal_summable_norm {M : ℝ} (hM : 0 < M) (e : E) :
    Summable (fun J : J₀ => ‖(sourceQuadraticRayCharacter F S₀ hζ e).allCoefficient J.val *
      (sourceQuadraticB2Bump ((Ideal.absNorm J.val : ℝ)/M) : ℂ)‖) := by
  let A : Finset J₀ := (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌊5*M/2⌋₊).toFinset.preimage
    (fun J : J₀ => J.val) Subtype.val_injective.injOn
  apply summable_of_ne_finset_zero (s := A)
  intro J hJ
  have hw : sourceQuadraticB2Bump ((Ideal.absNorm J.val : ℝ)/M) = 0 := by
    by_contra hn
    have hs := sourceQuadraticB2Bump_tsupport (subset_closure hn)
    have hupper : (Ideal.absNorm J.val : ℝ) ≤ 5*M/2 := by
      have hh := (div_le_iff₀ hM).mp hs.2
      linarith
    apply hJ
    simp only [A, Finset.mem_preimage, Set.Finite.mem_toFinset]
    exact (Nat.le_floor_iff (by positivity)).mpr hupper
  rw [hw, Complex.ofReal_zero, mul_zero, norm_zero]

/-- The small parity term is literally the signed squarefree ideal sum
with an unsigned square-ideal inner sum. -/
theorem sourceQuadraticBlockIdealSmall_eq_squarefree {M K : ℝ} (hM : 0 < M)
    (g e : E) :
    sourceQuadraticBlockIdealSmall F S₀ hζ M K g e =
      ∑' a : {J : Ideal (𝓞 F) // Squarefree J},
        if IsCoprime a.val (sourceQuadraticBlockBadIdeal F S₀) ∧
            IsCoprime a.val (I g) ∧ (Ideal.absNorm a.val : ℝ) ≤ K then
          (sourceQuadraticRayCharacter F S₀ hζ e).allCoefficient a.val *
            ∑' b : J₀, if IsCoprime b.val (sourceQuadraticBlockBadIdeal F S₀) ∧
                IsCoprime b.val (I g) ∧ IsCoprime b.val (sourceQuadraticConductor F S₀ hζ e) then
              (sourceQuadraticB2Bump ((Ideal.absNorm a.val : ℝ)*(Ideal.absNorm b.val : ℝ)^2/M) : ℂ)
              else 0
          else 0 := by
  have hquad (J : J₀) (hJ : IsCoprime J.val (sourceQuadraticConductor F S₀ hζ e)) :
      (sourceQuadraticRayCharacter F S₀ hζ e).allCoefficient J.val ^ 2 = 1 := by
    unfold EvenIdealRayCharacter.allCoefficient
    rw [dite_eq_left J.property, ite_eq_left hJ]
    exact congrArg Units.val (sourceQuadraticRayCharacter_sq F S₀ hζ e _)
  have h := quadraticHeckeSquarefreeNorm_tsum F (sourceQuadraticRayCharacter F S₀ hζ e)
    hquad (sourceQuadraticBlockBadIdeal F S₀ * I g) K M
    (fun t => (sourceQuadraticB2Bump t : ℂ))
    (sourceQuadraticBlockIdeal_summable_norm F S₀ hζ hM e)
  simpa only [sourceQuadraticBlockIdealSmall, IsCoprime.mul_right_iff, and_assoc] using h

/-- Direct B3-to-ideal correspondence on the actual finite column pairs. -/
theorem sourceQuadraticB3Block_eq_ideal_character_tails {M K : ℝ} (hM : 0 < M)
    (cols : Finset E) (a : E → ℂ) (g : E)
    (hcols : ∀ b ∈ cols, sourceReflectionIsSquarefree b) :
    sourceQuadraticB3Block F S₀ hζ (sourceQuadraticB2Rows F S₀ M K) cols
        (sourceQuadraticB2RowWeight F S₀ M) a g =
      ∑ p ∈ (cols ×ˢ cols).filter (fun p : E×E => p.1 ⊓ p.2 = g),
        star (a p.1)*a p.2*
          sourceQuadraticBlockIdealTail F S₀ hζ M K g ((p.1-g)+(p.2-g)) := by
  rw [sourceQuadraticB3Block_eq_character_rows F S₀ hζ _ _ _ _ _ hcols]
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨hpair,hg⟩ := Finset.mem_filter.mp hp
  obtain ⟨hb,hc⟩ := Finset.mem_product.mp hpair
  have hdis := ((sourceQuadratic_inf_eq_iff_quotient_disjoint F S₀ p.1 p.2 g).mp hg).2.2
  rw [sourceQuadraticBlockRowKernel_eq_idealTail F S₀ hζ hM g _
    (sourceQuadraticBlock_residual_squarefree F S₀ p.1 p.2 g (hcols p.1 hb) (hcols p.2 hc) hdis)]


/-- Full character sum minus the literal small-squarepart term, for every
pair in the common-g block. -/
theorem sourceQuadraticB3Block_eq_full_sub_small {M K : ℝ} (hM : 0 < M)
    (cols : Finset E) (a : E → ℂ) (g : E)
    (hcols : ∀ b ∈ cols, sourceReflectionIsSquarefree b) :
    sourceQuadraticB3Block F S₀ hζ (sourceQuadraticB2Rows F S₀ M K) cols
        (sourceQuadraticB2RowWeight F S₀ M) a g =
      ∑ p ∈ (cols ×ˢ cols).filter (fun p : E×E => p.1 ⊓ p.2 = g),
        star (a p.1)*a p.2*
          (sourceQuadraticBlockIdealFull F S₀ hζ M g ((p.1-g)+(p.2-g)) -
            sourceQuadraticBlockIdealSmall F S₀ hζ M K g ((p.1-g)+(p.2-g))) := by
  rw [sourceQuadraticB3Block_eq_ideal_character_tails F S₀ hζ hM cols a g hcols]
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨hpair,hg⟩ := Finset.mem_filter.mp hp
  obtain ⟨hb,hc⟩ := Finset.mem_product.mp hpair
  have hdis := ((sourceQuadratic_inf_eq_iff_quotient_disjoint F S₀ p.1 p.2 g).mp hg).2.2
  rw [sourceQuadraticBlockIdealTail_eq_full_sub_small F S₀ hζ hM g _
    (sourceQuadraticBlock_residual_squarefree F S₀ p.1 p.2 g (hcols p.1 hb) (hcols p.2 hc) hdis)]

end
end ArtinMatthews.SourceEulerAssembly
