Theorem po_with_one:
∀A. po A one ≅ A
Proof
cheat
QED

Theorem tp_eq:
∀f g. f∶ A×B → C ∧ g∶ A×B → C ⇒ (tp f = tp f' ⇔ f = f')
Proof
cheat
QED

Theorem tp_to_p:
 ⇒ tp f = fb
Proof
 
Theorem is_tp:
∀A B X f h. f∶ A×X → B ∧ h∶ X → exp A B ∧
            (ev A B) o ⟨p1 A X, h o (p2 A X)⟩ = f ⇒
            h = tp f
Proof
metis_tac[ax2]
QED

(*‘⟨p1 A N,(tp f ∘ s) ∘ p2 A N⟩ =
   ⟨p1 A N, (tp f) o (p2 A N)⟩ o ⟨p1 A N, s o (p2 A N)⟩’*)        
Theorem pcompose: (*decompose coposition of arrows lemma*)

Proof

Theorem ax2_conj2:
∀A B X f. f∶ (po A X) → B ⇒
          (∀h. (h∶ X → (exp A B) ∧
                (ev A B) o (pa (p1 A X) (h o (p2 A X))) = f) ⇔
                 h = tp f)
Proof
metis_tac[ax2]
QED                                  

Theorem pa_hom:
∀A B X f g. f∶ X→ A ∧ g∶ X→ B ⇒ ⟨f,g⟩∶ X → (A×B)
Proof
metis_tac[ax1_3]
QED
                                     

Theorem ev_hom:
∀A B X f. f∶ X → (exp A B) ⇒ (ev A B) o ⟨p1 A X,f o (p2 A X)⟩∶ (A×X) → B
Proof
rw[] >>
irule compose_hom >> qexists_tac ‘(po A (exp A B))’ >>
rw[] (* 2 *)
>- (irule pa_hom >> metis_tac[ax1_3,compose_hom])
>- metis_tac[ax2]
QED
                                             
Theorem ev_eq_eq:
∀A B X f g. f∶ X →(exp A B) ∧ g∶X → (exp A B) ∧
            (ev A B) o ⟨p1 A X,f o (p2 A X)⟩ =
            (ev A B) o ⟨p1 A X,g o (p2 A X)⟩ ⇒
            f = g
Proof
rw[] >>
‘f = tp ((ev A B) o ⟨p1 A X,f o (p2 A X)⟩)’ by
metis_tac[ax2]

Theorem compose_with_p1:        
∀A B X f. f∶ X→ (A×B) ⇒ p1 A B ∘ f ∶ X → A
Proof
metis_tac[ax1_3,compose_hom]
QED

Theorem compose_with_p2:        
∀A B X f. f∶ X→ (A×B) ⇒ p2 A B ∘ f ∶ X → B
Proof
metis_tac[ax1_3,compose_hom]
QED        
        
Theorem to_p_eq:
∀f g X A B. f∶ X → (A×B) ∧ g∶ X → (A × B) ⇒
            ((p1 A B) o f = (p1 A B) o g ∧ (p2 A B) o f = (p2 A B) o g ⇔ f = g)
Proof
rw[EQ_IMP_THM] >>
metis_tac[compose_with_p1,compose_with_p2,ax1_3]
QED                   


Theorem to_p_eq_applied:
∀f g X A B. f∶ X → (A×B) ∧ g∶ X → (A × B) ∧
         (p1 A B) o f = (p1 A B) o g ∧ (p2 A B) o f = (p2 A B) o g ⇒ f = g
Proof
metis_tac[to_p_eq]
QED

Theorem p1_hom[simp]:
∀A B. p1 A B∶ A×B → A
Proof
metis_tac[ax1_3]
QED


Theorem p2_hom[simp]:
∀A B. p2 A B∶ A×B → B
Proof
metis_tac[ax1_3]
QED                

Theorem p1_of_pa:
∀A B X f g. f∶ X → A ∧ g∶ X → B ⇒ (p1 A B) o ⟨f,g⟩ = f
Proof
metis_tac[ax1_3]
QED

Theorem p2_of_pa:
∀A B X f g. f∶ X → A ∧ g∶ X → B ⇒ (p2 A B) o ⟨f,g⟩ = g
Proof
metis_tac[ax1_3]
QED        


Theorem compose_assoc_SYM:
∀f g h A B C D. f∶A → B ∧ g∶B → C ∧ h∶C → D ⇒ h ∘ g ∘ f = (h ∘ g) ∘ f
Proof
metis_tac[compose_assoc]
QED
           
Theorem parallel_p_compose:
∀A B C D P Q f g i j. f∶ A → C ∧ g∶ B → D ∧ i∶ C → P ∧ j∶ D → Q ⇒
                      ⟨i o p1 C D,j o p2 C D⟩ o ⟨f o p1 A B, g o p2 A B⟩ =
                      ⟨i o f o p1 A B, j o g o p2 A B⟩
Proof
rw[] >> irule to_p_eq_applied >> qexistsl_tac [‘P’,‘Q’,‘A×B’] >>
‘⟨i ∘ f ∘ p1 A B,j ∘ g ∘ p2 A B⟩∶A×B → (P×Q)’
  by
   (‘i ∘ f ∘ p1 A B∶ (A×B) → P ∧ j ∘ g ∘ p2 A B∶ (A×B) → Q’
     suffices_by metis_tac[ax1_3] >>
     metis_tac[compose_hom,compose_assoc,ax1_3]) >>
(*??????*)
‘⟨i ∘ p1 C D,j ∘ p2 C D⟩ ∘ ⟨f ∘ p1 A B,g ∘ p2 A B⟩∶A×B → (P×Q)’
  by
   (irule compose_hom >> qexists_tac ‘C×D’ >>
   metis_tac[compose_hom,ax1_3]) >>
‘⟨f ∘ p1 A B,g ∘ p2 A B⟩∶ (A×B) → (C × D)’ by metis_tac[compose_hom,ax1_3] >>
‘⟨i ∘ p1 C D,j ∘ p2 C D⟩∶ (C × D) → (P × Q)’ by metis_tac[compose_hom,ax1_3] >>
‘p1 P Q ∘ ⟨i ∘ f ∘ p1 A B,j ∘ g ∘ p2 A B⟩  = i ∘ f ∘ p1 A B’
  by (irule p1_of_pa >> qexists_tac ‘A×B’ >>
     metis_tac[compose_hom,compose_assoc,ax1_3]) >>
‘p2 P Q ∘ ⟨i ∘ f ∘ p1 A B,j ∘ g ∘ p2 A B⟩ = j ∘ g ∘ p2 A B’
  by (irule p2_of_pa >> qexists_tac ‘A×B’ >>
     metis_tac[compose_hom,compose_assoc,ax1_3]) >>
fs[] >>
‘p1 P Q ∘ ⟨i ∘ p1 C D,j ∘ p2 C D⟩ = i ∘ p1 C D’
  by (irule p1_of_pa >> qexists_tac ‘C×D’ >>  metis_tac[compose_hom,ax1_3]) >>
‘p2 P Q ∘ ⟨i ∘ p1 C D,j ∘ p2 C D⟩ = j ∘ p2 C D’
   by (irule p2_of_pa >> qexists_tac ‘C×D’ >>  metis_tac[compose_hom,ax1_3]) >>
‘p1 P Q ∘ ⟨i ∘ p1 C D,j ∘ p2 C D⟩ ∘ ⟨f ∘ p1 A B,g ∘ p2 A B⟩ =
 (p1 P Q ∘ ⟨i ∘ p1 C D,j ∘ p2 C D⟩) ∘ ⟨f ∘ p1 A B,g ∘ p2 A B⟩’
 by (irule compose_assoc_SYM >> qexistsl_tac [‘A×B’,‘C×D’,‘P×Q’,‘P’] >>
    rw[] >> metis_tac[ax1_3]) >>
‘p2 P Q ∘ ⟨i ∘ p1 C D,j ∘ p2 C D⟩ ∘ ⟨f ∘ p1 A B,g ∘ p2 A B⟩ =
 (p2 P Q ∘ ⟨i ∘ p1 C D,j ∘ p2 C D⟩) ∘ ⟨f ∘ p1 A B,g ∘ p2 A B⟩’
 by (irule compose_assoc_SYM >> qexistsl_tac [‘A×B’,‘C×D’,‘P×Q’,‘Q’] >>
     rw[] >> metis_tac[ax1_3]) >>
‘(i ∘ p1 C D) ∘ ⟨f ∘ p1 A B,g ∘ p2 A B⟩ =
 i ∘ p1 C D ∘ ⟨f ∘ p1 A B,g ∘ p2 A B⟩’
  by metis_tac[compose_assoc,ax1_3] >>
‘(j ∘ p2 C D) ∘ ⟨f ∘ p1 A B,g ∘ p2 A B⟩ =
 j ∘ p2 C D ∘ ⟨f ∘ p1 A B,g ∘ p2 A B⟩’
  by metis_tac[compose_assoc,ax1_3] >>
fs[] >>
‘p1 C D ∘ ⟨f ∘ p1 A B,g ∘ p2 A B⟩ = f ∘ p1 A B’
  by (irule p1_of_pa >> qexists_tac ‘A×B’ >> simp[] >>
     metis_tac[compose_hom,ax1_3]) >>
‘p2 C D ∘ ⟨f ∘ p1 A B,g ∘ p2 A B⟩ = g ∘ p2 A B’
  by (irule p2_of_pa >> qexists_tac ‘A×B’ >> simp[] >>
     metis_tac[compose_hom,ax1_3]) >>
fs[]
QED

Theorem parallel_p_one_side:
∀A B C D f g.f∶ B → C ∧ g∶ C→ D ⇒
             ⟨p1 A B,g o f o p2 A B⟩ =
             ⟨p1 A C, g o p2 A C⟩ o ⟨p1 A B, f o p2 A B⟩
Proof
rw[] >> 
‘id A∶A → A ∧ f  B → D ∧ i∶C → P ∧ j∶D → Q ⇒
              ⟨i ∘ p1 C D,j ∘ p2 C D⟩ ∘ ⟨f ∘ p1 A B,g ∘ p2 A B⟩ =
              ⟨i ∘ f ∘ p1 A B,j ∘ g ∘ p2 A B⟩’
                           
                      
Theorem iterated_p_eq:
∀X A B C f g. f∶X → ((A×B)×C) ∧ g∶X → ((A×B)×C) ⇒
              (f = g ⇔
              (p1 A B) o (p1 (A×B) C) o f =  (p1 A B) o (p1 (A×B) C) o g ∧
              (p2 A B) o (p1 (A×B) C) o f =  (p2 A B) o (p1 (A×B) C) o g ∧
              (p2 (A×B) C) o f = (p2 (A×B) C) o g)
Proof
cheat
QED

Theorem iterated_p_eq_applied:
∀X A B C f g. f∶X → ((A×B)×C) ∧ g∶X → ((A×B)×C) ⇒
              ((p1 A B) o (p1 (A×B) C) o f =  (p1 A B) o (p1 (A×B) C) o g ∧
               (p2 A B) o (p1 (A×B) C) o f =  (p2 A B) o (p1 (A×B) C) o g ∧
               (p2 (A×B) C) o f = (p2 (A×B) C) o g ⇒ f = g)
Proof
cheat
QED
