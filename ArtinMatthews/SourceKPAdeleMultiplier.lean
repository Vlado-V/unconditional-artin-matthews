module

public import ArtinMatthews.SourceKPAdeleCoordinates
public import ArtinMatthews.SourceKPFiniteCompactTwist
public import ArtinMatthews.SourceKubotaRationalProduct


set_option backward.privateInPublic true
@[expose] public section

/-! The cubic Kubota cocycle on the actual finite adelic matrix group.
The local compact normalization makes the product finite for every
pair of finite adelic matrices. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups AdeleRing BigOperators
noncomputable section
variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPAdeleLocalMultiplier (g h : GL (Fin 2) 𝔸ᶠ[K])
    (P : HeightOneSpectrum (𝓞 K)) : rootsOfUnity 3 K :=
  (sourceKPRootsTransport K hζ P).symm (sourceKPFiniteTwistedMultiplier K hζ P
    (sourceKPAdeleMatrixAt K P g) (sourceKPAdeleMatrixAt K P h))

theorem sourceKPAdeleLocalMultiplier_cocycle (g h k : GL (Fin 2) 𝔸ᶠ[K])
    (P : HeightOneSpectrum (𝓞 K)) :
    sourceKPAdeleLocalMultiplier K hζ g h P * sourceKPAdeleLocalMultiplier K hζ (g * h) k P =
      sourceKPAdeleLocalMultiplier K hζ g (h * k) P * sourceKPAdeleLocalMultiplier K hζ h k P := by
  let e := sourceKPRootsTransport K hζ P
  let m := sourceKPAdeleMatrixAt K P
  have he := congrArg e.symm (sourceKPFiniteTwistedMultiplier_cocycle K hζ P (m g) (m h) (m k))
  simpa only [sourceKPAdeleLocalMultiplier, e, m, map_mul] using he

theorem sourceKPAdeleLocalMultiplier_hasFiniteMulSupport (g h : GL (Fin 2) 𝔸ᶠ[K]) :
    Function.HasFiniteMulSupport (sourceKPAdeleLocalMultiplier K hζ g h) := by
  apply Filter.eventually_cofinite.mp
  filter_upwards [sourceKPAdele_eventually_tame K, sourceKPAdeleMatrixAt_eventually_integral K g,
    sourceKPAdeleMatrixAt_eventually_integral K h] with P h6 hg hh
  rw [sourceKPAdeleLocalMultiplier, sourceKPFiniteTwistedMultiplier_of_integral K hζ P h6 _ _ hg hh, map_one]

theorem sourceKPAdeleLocalMultiplier_one_left (g : GL (Fin 2) 𝔸ᶠ[K]) (P : HeightOneSpectrum (𝓞 K)) :
    sourceKPAdeleLocalMultiplier K hζ 1 g P = 1 := by
  rw [sourceKPAdeleLocalMultiplier, map_one, sourceKPFiniteTwistedMultiplier_one_left, map_one]

theorem sourceKPAdeleLocalMultiplier_one_right (g : GL (Fin 2) 𝔸ᶠ[K]) (P : HeightOneSpectrum (𝓞 K)) :
    sourceKPAdeleLocalMultiplier K hζ g 1 P = 1 := by
  rw [sourceKPAdeleLocalMultiplier, map_one, sourceKPFiniteTwistedMultiplier_one_right, map_one]

def sourceKPAdeleMultiplier (g h : GL (Fin 2) 𝔸ᶠ[K]) : rootsOfUnity 3 K :=
  ∏ᶠ P, sourceKPAdeleLocalMultiplier K hζ g h P

theorem sourceKPAdeleMultiplier_cocycle (g h k : GL (Fin 2) 𝔸ᶠ[K]) :
    sourceKPAdeleMultiplier K hζ g h * sourceKPAdeleMultiplier K hζ (g * h) k =
      sourceKPAdeleMultiplier K hζ g (h * k) * sourceKPAdeleMultiplier K hζ h k := by
  unfold sourceKPAdeleMultiplier
  rw [← finprod_mul_distrib (sourceKPAdeleLocalMultiplier_hasFiniteMulSupport K hζ g h)
    (sourceKPAdeleLocalMultiplier_hasFiniteMulSupport K hζ (g * h) k),
    ← finprod_mul_distrib (sourceKPAdeleLocalMultiplier_hasFiniteMulSupport K hζ g (h * k))
      (sourceKPAdeleLocalMultiplier_hasFiniteMulSupport K hζ h k)]
  exact finprod_congr (sourceKPAdeleLocalMultiplier_cocycle K hζ g h k)

theorem sourceKPAdeleMultiplier_one_left (g : GL (Fin 2) 𝔸ᶠ[K]) : sourceKPAdeleMultiplier K hζ 1 g = 1 := by
  simp only [sourceKPAdeleMultiplier, sourceKPAdeleLocalMultiplier_one_left, finprod_one]

theorem sourceKPAdeleMultiplier_one_right (g : GL (Fin 2) 𝔸ᶠ[K]) : sourceKPAdeleMultiplier K hζ g 1 = 1 := by
  simp only [sourceKPAdeleMultiplier, sourceKPAdeleLocalMultiplier_one_right, finprod_one]

theorem sourceKPAdeleMatrixAt_scalar (P : HeightOneSpectrum (𝓞 K)) (u : 𝔸ᶠ[K]ˣ) :
    sourceKPAdeleMatrixAt K P (GeneralLinearGroup.scalar (Fin 2) u) =
      GeneralLinearGroup.scalar (Fin 2) (Units.map (sourceKPAdeleEval K P).toMonoidHom u) :=
  GeneralLinearGroup.map_scalar (sourceKPAdeleEval K P) u

theorem sourceKPAdeleMultiplier_scalar_pair (u v : 𝔸ᶠ[K]ˣ) :
    sourceKPAdeleMultiplier K hζ (GeneralLinearGroup.scalar (Fin 2) u)
      (GeneralLinearGroup.scalar (Fin 2) v) = 1 := by
  rw [sourceKPAdeleMultiplier, ← finprod_one (α := HeightOneSpectrum (𝓞 K))]
  apply finprod_congr
  intro P
  rw [sourceKPAdeleLocalMultiplier, sourceKPAdeleMatrixAt_scalar, sourceKPAdeleMatrixAt_scalar,
    sourceKPFiniteTwistedMultiplier_scalar_pair, map_one]

theorem sourceKPAdeleMultiplier_scalar_comm (g : GL (Fin 2) 𝔸ᶠ[K]) (u : 𝔸ᶠ[K]ˣ) :
    sourceKPAdeleMultiplier K hζ (GeneralLinearGroup.scalar (Fin 2) u) g =
      sourceKPAdeleMultiplier K hζ g (GeneralLinearGroup.scalar (Fin 2) u) := by
  unfold sourceKPAdeleMultiplier
  apply finprod_congr
  intro P
  rw [sourceKPAdeleLocalMultiplier, sourceKPAdeleLocalMultiplier, sourceKPAdeleMatrixAt_scalar,
    sourceKPFiniteTwistedMultiplier_scalar_comm]

end
end ArtinMatthews
