module

public import ArtinMatthews.SourcePrincipalBallCoset
public import ArtinMatthews.SourceComplexIdealSummability


set_option backward.privateInPublic true
@[expose] public section

/-! Reindex a periodic lattice sum by its actual finite quotient.
Absolute convergence is inherited from the literal shifted ideal sums. -/
namespace ArtinMatthews.SourcePhysical

open NumberField NumberField.InfinitePlace IsDedekindDomain
open VaryingKummerAnalytic SIntegerPrincipalization
open scoped NumberField Classical nonZeroDivisors SchwartzMap
noncomputable section
variable (K : Type) [Field K] [NumberField K]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))

local notation "S" => principalizingSet S₀
local notation "d" => principalizingDenominator S₀
local notation "CPlaces" => {v : InfinitePlace K // IsComplex v}

theorem sourceComplexFieldEmbedding_add (a b : K) :
    sourceComplexFieldEmbedding K (a + b) =
      sourceComplexFieldEmbedding K a + sourceComplexFieldEmbedding K b := by
  funext v
  exact map_add v.val.embedding a b

def sourcePrincipalBallWeightedTerm (e : S → ℤ) (M : Ideal (𝓞 K))
    (w : sourcePrincipalBallModulusQuotient K S₀ M → ℂ) (f : CPlaces → 𝓢(ℂ, ℂ))
    (x : (sourceFiniteBallIdeal K S e).val) : ℂ :=
  w (sourcePrincipalBallIdealToQuotient K S₀ e M x) *
    sourceComplexTensor f (sourceComplexFieldEmbedding K (x : K))

theorem sourcePrincipalBallWeightedTerm_coset (e : S → ℤ) (M : Ideal (𝓞 K))
    (hM : M ≠ ⊥) (hc : IsCoprime M (Ideal.span {d}))
    (w : sourcePrincipalBallModulusQuotient K S₀ M → ℂ) (f : CPlaces → 𝓢(ℂ, ℂ))
    (q : sourcePrincipalBallModulusQuotient K S₀ M)
    (y : (sourcePrincipalBallProductUnit K S₀ e M hM).val.val) :
    sourcePrincipalBallWeightedTerm K S₀ e M w f (sourcePrincipalBallCosetEquiv K S₀ e M hM hc (q, y)) =
      w q * sourceComplexTensor f
        (sourceComplexFieldEmbedding K (sourcePrincipalBallCosetRepresentative K S₀ e M hc q : K) +
          sourceComplexFieldEmbedding K (y : K)) := by
  unfold sourcePrincipalBallWeightedTerm
  rw [sourcePrincipalBallCosetEquiv_quotient,
    sourcePrincipalBallCosetEquiv_val, sourceComplexFieldEmbedding_add]

variable [IsTotallyComplex K]

theorem sourcePrincipalBallWeightedTerm_coset_summable_norm (e : S → ℤ) (M : Ideal (𝓞 K))
    (hM : M ≠ ⊥) (hc : IsCoprime M (Ideal.span {d}))
    (w : sourcePrincipalBallModulusQuotient K S₀ M → ℂ) (f : CPlaces → 𝓢(ℂ, ℂ))
    (q : sourcePrincipalBallModulusQuotient K S₀ M) :
    Summable (fun y : (sourcePrincipalBallProductUnit K S₀ e M hM).val.val =>
      ‖sourcePrincipalBallWeightedTerm K S₀ e M w f
        (sourcePrincipalBallCosetEquiv K S₀ e M hM hc (q, y))‖) := by
  simp_rw [sourcePrincipalBallWeightedTerm_coset, norm_mul]
  exact (sourceComplexIdealTensor_summable_norm K _ f
    (sourceComplexFieldEmbedding K (sourcePrincipalBallCosetRepresentative K S₀ e M hc q : K))).mul_left _

theorem sourcePrincipalBallWeightedTerm_summable_norm (e : S → ℤ) (M : Ideal (𝓞 K))
    (hM : M ≠ ⊥) (hc : IsCoprime M (Ideal.span {d}))
    (w : sourcePrincipalBallModulusQuotient K S₀ M → ℂ) (f : CPlaces → 𝓢(ℂ, ℂ)) :
    Summable (fun x : (sourceFiniteBallIdeal K S e).val => ‖sourcePrincipalBallWeightedTerm K S₀ e M w f x‖) := by
  let : Finite (sourcePrincipalBallModulusQuotient K S₀ M) :=
    sourcePrincipalBallModulusQuotient_finite K S₀ M hM hc
  exact sourceFiniteCoset_summable_norm (sourcePrincipalBallCosetEquiv K S₀ e M hM hc) _
    (sourcePrincipalBallWeightedTerm_coset_summable_norm K S₀ e M hM hc w f)

theorem sourcePrincipalBallWeightedSum_reindex (e : S → ℤ) (M : Ideal (𝓞 K))
    (hM : M ≠ ⊥) (hc : IsCoprime M (Ideal.span {d}))
    (w : sourcePrincipalBallModulusQuotient K S₀ M → ℂ) (f : CPlaces → 𝓢(ℂ, ℂ)) :
    (∑' x : (sourceFiniteBallIdeal K S e).val, sourcePrincipalBallWeightedTerm K S₀ e M w f x) =
      ∑' q : sourcePrincipalBallModulusQuotient K S₀ M, w q *
        ∑' y : (sourcePrincipalBallProductUnit K S₀ e M hM).val.val,
          sourceComplexTensor f
            (sourceComplexFieldEmbedding K (sourcePrincipalBallCosetRepresentative K S₀ e M hc q : K) +
              sourceComplexFieldEmbedding K (y : K)) := by
  let : Finite (sourcePrincipalBallModulusQuotient K S₀ M) :=
    sourcePrincipalBallModulusQuotient_finite K S₀ M hM hc
  rw [sourceFiniteCoset_tsum (sourcePrincipalBallCosetEquiv K S₀ e M hM hc) _
    (sourcePrincipalBallWeightedTerm_coset_summable_norm K S₀ e M hM hc w f)]
  simp_rw [sourcePrincipalBallWeightedTerm_coset, tsum_mul_left]

end
end ArtinMatthews.SourcePhysical
