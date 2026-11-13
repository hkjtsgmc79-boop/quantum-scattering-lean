/- Q4: exact compatibility with the historically verified below-barrier project.
No original Q2 module or original public theorem is changed by this addition. -/
import QuantumTunneling.EnergyRegimes
import QuantumTunneling.CompleteStatement

noncomputable section
namespace QuantumTunneling
namespace RectangularParameters

def asBelow (p : RectangularParameters) (h : p.energy<p.height) : Parameters :=
  ⟨p.hbar,p.mass,p.energy,p.height,p.width,p.hbar_pos,p.mass_pos,p.energy_pos,h,p.width_pos⟩

lemma A_eq_Q2 (p : RectangularParameters) (h : p.energy<p.height) :
    p.layer.A=(p.asBelow h).spectral.incidentAmplitude := by
  change (⟨p.profile.C p.width,
      -((p.k^2+p.profile.delta)/(2*p.k))*p.profile.S p.width⟩ : ℂ)=
    (⟨Real.cosh (p.kappa*p.width),
      ((p.kappa/p.k-p.k/p.kappa)/2)*Real.sinh (p.kappa*p.width)⟩ : ℂ)
  rw [p.profile_below h]
  apply Complex.ext <;> dsimp [PropagationProfile.evanescent]
    <;> field_simp [ne_of_gt p.k_pos,ne_of_gt (p.kappa_pos h)] <;> ring
lemma B_eq_Q2 (p : RectangularParameters) (h : p.energy<p.height) :
    p.layer.B=(p.asBelow h).spectral.reflectedAmplitude := by
  change (⟨0,((p.profile.delta-p.k^2)/(2*p.k))*p.profile.S p.width⟩ : ℂ)=
    (⟨0,-((p.kappa/p.k+p.k/p.kappa)/2)*Real.sinh (p.kappa*p.width)⟩ : ℂ)
  rw [p.profile_below h]
  apply Complex.ext <;> dsimp [PropagationProfile.evanescent]
    <;> field_simp [ne_of_gt p.k_pos,ne_of_gt (p.kappa_pos h)] <;> ring

/-- The new normalized below-barrier wave is the old wave, not a weaker proxy. -/
theorem wave_eq_Q2 (p : RectangularParameters) (h : p.energy<p.height) :
    p.wave=(p.asBelow h).spectral.normalizedWave := by
  have hL : p.layer.left=(p.asBelow h).spectral.left := by
    funext x
    change freeWave p.k p.layer.A p.layer.B x=_
    rw [p.A_eq_Q2 h,p.B_eq_Q2 h]
    rfl
  have hI : p.layer.inside=(p.asBelow h).spectral.inside := by
    funext x
    rw [p.inside_below h]
    rfl
  have hR : p.layer.right=(p.asBelow h).spectral.right := by rfl
  funext x
  change (join 0 p.layer.left (join p.width p.layer.inside p.layer.right) x)/p.layer.A =
    (join 0 (p.asBelow h).spectral.left
      (join p.width (p.asBelow h).spectral.inside (p.asBelow h).spectral.right) x)/
        (p.asBelow h).spectral.incidentAmplitude
  rw [hL,hI,hR,p.A_eq_Q2 h]

lemma transmission_eq_Q2 (p : RectangularParameters) (h : p.energy<p.height) :
    p.layer.T=(p.asBelow h).spectral.transmission := by
  rw [p.layer.T_as_inv,p.A_eq_Q2 h]
  simp only [Spectral.transmission,one_div]

end RectangularParameters
end QuantumTunneling
