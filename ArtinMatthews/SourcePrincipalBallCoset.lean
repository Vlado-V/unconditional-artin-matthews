module

public import ArtinMatthews.SourcePrincipalBallQuotientKernel
public import ArtinMatthews.SourceFiniteCosetTools


set_option backward.privateInPublic true
@[expose] public section

/-! Exact cosets for the genuine principal S-integer quotient. The
translated lattice is the quotient kernel computed by valuations. -/
namespace ArtinMatthews.SourcePhysical

open NumberField IsDedekindDomain FractionalIdeal SIntegerPrincipalization SIntegerQuotient
open scoped NumberField Classical nonZeroDivisors
noncomputable section
variable (K : Type) [Field K] [NumberField K]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))

local notation "FI" => FractionalIdeal (𝓞 K)⁰ K
local notation "S" => principalizingSet S₀
local notation "OS" => PrincipalIntegerRing S₀
local notation "d" => principalizingDenominator S₀

abbrev sourcePrincipalBallModulusQuotient (M : Ideal (𝓞 K)) :=
  OS ⧸ M.map (algebraMap (𝓞 K) OS)

theorem sourcePrincipalBallModulusQuotient_finite (M : Ideal (𝓞 K)) (hM : M ≠ ⊥)
    (hc : IsCoprime M (Ideal.span {d})) :
    Finite (sourcePrincipalBallModulusQuotient K S₀ M) := by
  let : Finite ((𝓞 K) ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient hM
  exact Finite.of_surjective _ (principalQuotientEquiv S₀ M hc).surjective

def sourcePrincipalBallProductUnit (e : S → ℤ) (M : Ideal (𝓞 K)) (hM : M ≠ ⊥) : FIˣ :=
  Units.mk0 ((M : FI) * sourceFiniteBallIdeal K S e)
    (mul_ne_zero (FractionalIdeal.coeIdeal_ne_zero.mpr hM) (sourceFiniteBallIdeal_ne_zero K S e))

theorem sourcePrincipalBallProductUnit_val (e : S → ℤ) (M : Ideal (𝓞 K)) (hM : M ≠ ⊥) :
    (sourcePrincipalBallProductUnit K S₀ e M hM).val = (M : FI) * sourceFiniteBallIdeal K S e := rfl

def sourcePrincipalBallProductIncl (e : S → ℤ) (M : Ideal (𝓞 K)) (hM : M ≠ ⊥)
    (hc : IsCoprime M (Ideal.span {d})) :
    (sourcePrincipalBallProductUnit K S₀ e M hM).val.val →+ (sourceFiniteBallIdeal K S e).val where
  toFun y := ⟨(y : K), ((sourcePrincipalExteriorBallProduct_mem_iff K S₀ e M hM hc _).mp y.property).1⟩
  map_zero' := rfl
  map_add' _ _ := rfl

theorem sourcePrincipalBallProductIncl_injective (e : S → ℤ) (M : Ideal (𝓞 K)) (hM : M ≠ ⊥)
    (hc : IsCoprime M (Ideal.span {d})) :
    Function.Injective (sourcePrincipalBallProductIncl K S₀ e M hM hc) := by
  intro y z h
  apply Subtype.ext
  exact congrArg (fun x : (sourceFiniteBallIdeal K S e).val => (x : K)) h

theorem sourcePrincipalBallProductIncl_fiber (e : S → ℤ) (M : Ideal (𝓞 K)) (hM : M ≠ ⊥)
    (hc : IsCoprime M (Ideal.span {d})) (x : (sourceFiniteBallIdeal K S e).val) :
    sourcePrincipalBallIdealToQuotient K S₀ e M x = 0 ↔
      ∃ y, sourcePrincipalBallProductIncl K S₀ e M hM hc y = x := by
  refine (sourcePrincipalBallIdealToQuotient_eq_zero_iff K S₀ e M hM hc x).trans ?_
  constructor
  · intro h
    exact ⟨⟨(x : K), h⟩, Subtype.ext rfl⟩
  · rintro ⟨y, rfl⟩
    exact y.property

def sourcePrincipalBallCosetRepresentative (e : S → ℤ) (M : Ideal (𝓞 K))
    (hc : IsCoprime M (Ideal.span {d})) (q : sourcePrincipalBallModulusQuotient K S₀ M) :
    (sourceFiniteBallIdeal K S e).val :=
  sourceAdditiveCosetRepresentative (sourcePrincipalBallIdealToQuotient K S₀ e M)
    (sourcePrincipalBallIdealToQuotient_surjective K S₀ e M hc) q

theorem sourcePrincipalBallCosetRepresentative_spec (e : S → ℤ) (M : Ideal (𝓞 K))
    (hc : IsCoprime M (Ideal.span {d})) (q : sourcePrincipalBallModulusQuotient K S₀ M) :
    sourcePrincipalBallIdealToQuotient K S₀ e M (sourcePrincipalBallCosetRepresentative K S₀ e M hc q) = q :=
  sourceAdditiveCosetRepresentative_spec _ _ _

def sourcePrincipalBallCosetEquiv (e : S → ℤ) (M : Ideal (𝓞 K)) (hM : M ≠ ⊥)
    (hc : IsCoprime M (Ideal.span {d})) :
    sourcePrincipalBallModulusQuotient K S₀ M × (sourcePrincipalBallProductUnit K S₀ e M hM).val.val ≃
      (sourceFiniteBallIdeal K S e).val :=
  sourceAdditiveCosetEquiv (sourcePrincipalBallIdealToQuotient K S₀ e M)
    (sourcePrincipalBallIdealToQuotient_surjective K S₀ e M hc)
    (sourcePrincipalBallProductIncl K S₀ e M hM hc)
    (sourcePrincipalBallProductIncl_injective K S₀ e M hM hc)
    (sourcePrincipalBallProductIncl_fiber K S₀ e M hM hc)

theorem sourcePrincipalBallCosetEquiv_val (e : S → ℤ) (M : Ideal (𝓞 K)) (hM : M ≠ ⊥)
    (hc : IsCoprime M (Ideal.span {d})) (q : sourcePrincipalBallModulusQuotient K S₀ M)
    (y : (sourcePrincipalBallProductUnit K S₀ e M hM).val.val) :
    (sourcePrincipalBallCosetEquiv K S₀ e M hM hc (q, y) : K) =
      (sourcePrincipalBallCosetRepresentative K S₀ e M hc q : K) + (y : K) := rfl

theorem sourcePrincipalBallCosetEquiv_quotient (e : S → ℤ) (M : Ideal (𝓞 K)) (hM : M ≠ ⊥)
    (hc : IsCoprime M (Ideal.span {d})) (q : sourcePrincipalBallModulusQuotient K S₀ M)
    (y : (sourcePrincipalBallProductUnit K S₀ e M hM).val.val) :
    sourcePrincipalBallIdealToQuotient K S₀ e M (sourcePrincipalBallCosetEquiv K S₀ e M hM hc (q, y)) = q := by
  change sourcePrincipalBallIdealToQuotient K S₀ e M
    (sourcePrincipalBallCosetRepresentative K S₀ e M hc q +
      sourcePrincipalBallProductIncl K S₀ e M hM hc y) = q
  let p := sourcePrincipalBallIdealToQuotient K S₀ e M
  let a := sourcePrincipalBallCosetRepresentative K S₀ e M hc q
  let b := sourcePrincipalBallProductIncl K S₀ e M hM hc y
  have ha : p a = q := sourcePrincipalBallCosetRepresentative_spec K S₀ e M hc q
  have hb : p b = 0 := (sourcePrincipalBallProductIncl_fiber K S₀ e M hM hc _).mpr ⟨y, rfl⟩
  exact (p.map_add a b).trans (by rw [ha, hb, add_zero])

end
end ArtinMatthews.SourcePhysical
