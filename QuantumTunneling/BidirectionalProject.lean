/-
Q5 WHOLE-PROJECT TARGET. This is an output specification and proof candidate,
not evidence of a successful Lean run. No field below is an input hypothesis.
No time-dependent or self-adjoint-operator spectral completeness claim is made.
-/
import QuantumTunneling.ScatteringContinuity
import QuantumTunneling.RadiationAtInfinity

noncomputable section
open Filter Set
open scoped Topology
namespace QuantumTunneling

/-- Physical function class with literal potential, actual derivatives and open
exterior radiation conditions. There is NO interior basis ansatz in this class. -/
def PhysicalScattering (hbar mass energy height width:ℝ)
    (iL iR:ℂ) (f:ℝ→ℂ) : Prop :=
  ContDiff ℝ 1 f ∧
  (∀ x, x≠0 → x≠width → DifferentiableAt ℝ (deriv f) x) ∧
  (∀ x, x≠0 → x≠width →
    (-(hbar^2/(2*mass)):ℝ) • deriv (deriv f) x+
      (if 0≤x ∧ x≤width then height else 0) • f x=energy • f x) ∧
  ∃ oL oR:ℂ,
    (∀ x, x<0 → f x=iL*plane (Real.sqrt (2*mass*energy)/hbar) x+
      oL*plane (-(Real.sqrt (2*mass*energy)/hbar)) x) ∧
    (∀ x, width<x → f x=oR*plane (Real.sqrt (2*mass*energy)/hbar) (x-width)+
      iR*plane (-(Real.sqrt (2*mass*energy)/hbar)) (x-width))

lemma admissible_iff_physical (p:RectangularParameters) (iL iR:ℂ) (f:ℝ→ℂ) :
    AdmissibleScattering p iL iR f ↔
      PhysicalScattering p.hbar p.mass p.energy p.height p.width iL iR f := by
  constructor
  · rintro ⟨hs,oL,oR,hr⟩
    refine ⟨hs.regularity,?_,hs.schrodinger,oL,oR,hr.left,hr.right⟩
    intro x h0 ha
    exact (hs.equation x h0 ha).differentiableAt
  · rintro ⟨hc,hd,he,oL,oR,hl,hr⟩
    refine ⟨StationaryState.of_schrodinger hc hd he,oL,oR,?_⟩
    exact ⟨hl,hr⟩

/-- Public existence and uniqueness theorem with only five positive physical
numbers and two arbitrary complex incoming amplitudes as inputs. -/
theorem existsUnique_physical_two_sided_scattering
    (hbar mass energy height width:ℝ)
    (hh:0<hbar) (hm:0<mass) (hE:0<energy) (hV:0<height) (ha:0<width)
    (iL iR:ℂ) :
    ∃! f:ℝ→ℂ, PhysicalScattering hbar mass energy height width iL iR f := by
  let p:RectangularParameters:=⟨hbar,mass,energy,height,width,hh,hm,hE,hV,ha⟩
  obtain ⟨f,hf,hu⟩ := existsUnique_two_sided_state p iL iR
  refine ⟨f,(admissible_iff_physical p iL iR f).mp hf,?_⟩
  intro g hg
  exact hu g ((admissible_iff_physical p iL iR g).mpr hg)

/-- A finite, explicit acceptance target. Further wavepacket or operator theory
is outside this target, not an indefinitely postponed condition of completion. -/
structure BidirectionalProjectCertificate (p:RectangularParameters) : Prop where
  all_energy_left : RectangularScatteringCertificate p p.wave p.waveD
    p.reflectionAmplitude p.transmissionAmplitude
  general_unique : ∀ iL iR:ℂ, ∃! f:ℝ→ℂ,
    PhysicalScattering p.hbar p.mass p.energy p.height p.width iL iR f
  infinity_unique : ∀ iL iR:ℂ, ∃! f:ℝ→ℂ, IncomingAtInfinity p iL iR f
  infinity_exact_equivalence : ∀ iL iR f,
    IncomingAtInfinity p iL iR f ↔ AdmissibleScattering p iL iR f
  exterior_basis_derived : ∀ f:ℝ→ℂ, StationaryState p f →
    TwoSidedRadiation p f (rightChannel p 0 f (-1))
      (leftChannel p p.width f (p.width+1))
      (leftChannel p 0 f (-1)) (rightChannel p p.width f (p.width+1))
  explicit_coherent_state : ∀ iL iR, StationaryState p (p.coherentWave iL iR)
  coherent_radiation : ∀ iL iR,
    TwoSidedRadiation p (p.coherentWave iL iR) iL iR
      (p.layer.outgoingLeft iL iR) (p.layer.outgoingRight iL iR)
  actual_matrix_action : ∀ iL iR,
    p.layer.scatteringMatrix.mulVec ![iL,iR]=
      ![p.layer.outgoingLeft iL iR,p.layer.outgoingRight iL iR]
  unitary_left : p.layer.scatteringMatrix.conjTranspose*p.layer.scatteringMatrix=1
  unitary_right : p.layer.scatteringMatrix*p.layer.scatteringMatrix.conjTranspose=1
  reciprocal : p.layer.scatteringMatrix.transpose=p.layer.scatteringMatrix
  phase_cancellation : star p.layer.reflectionAmplitude*p.layer.transmissionAmplitude+
    star p.layer.transmissionAmplitude*p.layer.reflectionAmplitude=0
  coherent_norm : ∀ iL iR,
    absSq (p.layer.outgoingLeft iL iR)+absSq (p.layer.outgoingRight iL iR)=
      absSq iL+absSq iR
  current_left : ∀ iL iR x, current p.hbar p.mass (p.coherentWave iL iR) x=
    (p.hbar/p.mass)*p.k*(absSq iL-absSq (p.layer.outgoingLeft iL iR))
  current_right : ∀ iL iR x, current p.hbar p.mass (p.coherentWave iL iR) x=
    (p.hbar/p.mass)*p.k*(absSq (p.layer.outgoingRight iL iR)-absSq iR)
  pure_right_current : ∀ x, current p.hbar p.mass p.rightWave x=
    -((p.hbar/p.mass)*p.k*p.layer.T)
  transfer_determinant : p.layer.transferMatrix.det=1
  physical_scalar_bridge : p.layer.T=
    transmissionFunction p.hbar p.mass p.height p.width p.energy
  physical_matrix_bridge : p.layer.scatteringMatrix=
    energyScatteringMatrix p.hbar p.mass p.height p.width p.energy
  threshold_limit : Tendsto (transmissionFunction p.hbar p.mass p.height p.width)
    (𝓝 p.height) (𝓝 ((1+p.mass*p.height*p.width^2/(2*p.hbar^2))⁻¹))
  threshold_matrix : ∀ i j:Fin 2,
    ContinuousAt (fun E=>energyScatteringMatrix p.hbar p.mass p.height p.width E i j) p.height
  all_resonant_widths : p.layer.T=1 ↔ p.height<p.energy ∧
    ∃! n:ℕ, p.width=resonantWidth p.q n
  all_resonant_energies : p.layer.T=1 ↔ ∃! n:ℕ, p.energy=p.resonantEnergy n
  resonant_energies_distinct : StrictMono p.resonantEnergy
  thin_limit : Tendsto (fun a:ℝ=>transmissionFunction p.hbar p.mass p.height a p.energy)
    (𝓝 0) (𝓝 1)
  high_energy_limit : Tendsto (transmissionFunction p.hbar p.mass p.height p.width)
    atTop (𝓝 1)
  high_energy_bound : ∀ E, 2*p.height<E →
    0≤1-transmissionFunction p.hbar p.mass p.height p.width E ∧
    1-transmissionFunction p.hbar p.mass p.height p.width E≤p.height^2/(2*E^2)
  thick_limit : p.energy<p.height →
    Tendsto (fun a:ℝ=>transmissionFunction p.hbar p.mass p.height a p.energy)
      atTop (𝓝 0)
  thick_prefactor : p.energy<p.height →
    Tendsto (fun a:ℝ=>transmissionFunction p.hbar p.mass p.height a p.energy*
      Real.exp (2*(p.kappa*a))) atTop
      (𝓝 (16*p.energy*(p.height-p.energy)/p.height^2))
  no_spontaneous_outgoing : ∀ f:ℝ→ℂ, AdmissibleScattering p 0 0 f → f=0

/-- Whole-project theorem: all advertised core branches are filled by proofs.
Compilation, axiom audit and independent semantic review remain distinct gates. -/
theorem rectangular_barrier_bidirectional_project (p:RectangularParameters) :
    BidirectionalProjectCertificate p where
  all_energy_left := complete_rectangular_scattering p
  general_unique := existsUnique_physical_two_sided_scattering
    p.hbar p.mass p.energy p.height p.width p.hbar_pos p.mass_pos
      p.energy_pos p.height_pos p.width_pos
  infinity_unique := existsUnique_incoming_at_infinity p
  infinity_exact_equivalence := incoming_at_infinity_iff_admissible p
  exterior_basis_derived := fun f hf=>hf.derived_exterior_modes
  explicit_coherent_state := p.coherentWave_stationary
  coherent_radiation := coherentWave_radiation p
  actual_matrix_action := p.layer.outgoing_eq_matrix
  unitary_left := p.layer.scatteringMatrix_unitary.1
  unitary_right := p.layer.scatteringMatrix_unitary.2
  reciprocal := p.layer.scatteringMatrix_symmetric
  phase_cancellation := p.layer.off_diagonal_zero
  coherent_norm := p.layer.coherent_probability_balance
  current_left := coherent_current_value p
  current_right := coherent_current_right p
  pure_right_current := p.current_rightWave
  transfer_determinant := p.layer.transfer_det_one
  physical_scalar_bridge := p.physical_transmission_regularized
  physical_matrix_bridge := p.physical_matrix_regularized
  threshold_limit := transmission_threshold_limit p.hbar_pos p.mass_pos p.height_pos
  threshold_matrix := scatteringMatrix_threshold_continuity p.hbar_pos p.mass_pos p.height_pos
  all_resonant_widths := p.complete_resonance_classification
  all_resonant_energies := p.complete_resonant_energy_classification
  resonant_energies_distinct := p.resonantEnergy_strictMono
  thin_limit := transmission_thin_limit _ _ _ _
  high_energy_limit := transmission_high_energy_limit p.hbar_pos p.mass_pos p.height_pos p.width_pos
  high_energy_bound := fun E hE=>transmission_high_energy_bound
    p.hbar_pos p.mass_pos p.height_pos p.width_pos hE
  thick_limit := fun hE=>transmission_thick_limit p.hbar_pos p.mass_pos p.energy_pos hE
  thick_prefactor := fun hE=>transmission_thick_scaled_limit p.hbar_pos p.mass_pos p.energy_pos hE
  no_spontaneous_outgoing := no_outgoing_only_solution p

/-- Stable release gate: purely physical inputs, no supplied wave, profile,
unitarity hypothesis, continuity hypothesis or elementary ansatz. -/
theorem rectangular_barrier_complete_stationary_theory
    (hbar mass energy height width:ℝ)
    (hh:0<hbar) (hm:0<mass) (hE:0<energy) (hV:0<height) (ha:0<width) :
    BidirectionalProjectCertificate
      (⟨hbar,mass,energy,height,width,hh,hm,hE,hV,ha⟩:RectangularParameters) :=
  rectangular_barrier_bidirectional_project _

end QuantumTunneling
