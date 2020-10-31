val _ = new_type ("arrow", 0)
val _ = new_type ("object", 0)
val _ = new_constant("dom", “:arrow -> object”)
val _ = new_constant("cod", “:arrow -> object”)
open HolKernel Parse boolLib bossLib;


Definition hom_def:
hom f X Y ⇔ dom f = X ∧ cod f = Y 
End                                                   
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Infix (NONASSOC,450), 
                  pp_elements = [TOK "∶",TM,HardSpace 1,TOK "→",BreakSpace (1,0)], 
                  term_name = "hom", paren_style = OnlyIfNecessary}


val _ = new_constant("id", ``:object -> arrow``)                      
val id1 = new_axiom("id1", ``!X. id X ∶ X → X``) 
val _ = export_rewrites["id1"]        
        
val _ = new_constant("compose", ``:arrow -> arrow -> arrow``);
Overload "o" = ``compose``



val idL0 = new_axiom("idL0", ``!X a. cod a = X ==> (id X) o a = a``);

Theorem idL[simp]:
∀f X Y. f∶X→Y ==> (id Y) o f = f
Proof
metis_tac[idL0,hom_def]
QED

val idR0 = new_axiom("idR0", ``!X a. dom a = X ==> a o (id X) = a``);

Theorem idR[simp]:
∀f X Y. f∶X→Y ==> f o (id X) = f
Proof
rw[idR0,hom_def]          
QED

val compose_hom0 = new_axiom("compose_hom0",
                            ``!f g. cod f = dom g ⇒
                                    dom (g o f) = dom f ∧
                                    cod (g o f) = cod g``);

Theorem compose_hom[simp]:
∀f g A B C. f∶ A → B ∧ g∶ B → C ⇒  g o f∶ A→ C
Proof
rw[compose_hom0,hom_def]
QED
                  
val compose_assoc0 = new_axiom("compose_assoc0",
                  “∀f g h. cod f = dom g ∧ cod g = dom h ⇒
                           (h o g) o f = h o (g o f)”)

Theorem compose_assoc[simp]:
∀f g h A B C D. f∶A → B ∧ g∶B → C ∧ h∶C→ D ⇒
                (h o g) o f = h o (g o f)
Proof
rw[compose_assoc0,hom_def]
QED


(*ax1 all finite root exists, initial, terminal, prod, coprod, eq, coeq*)

val _ = new_constant("one",“:object”)

(* X --t_x--> 1*)

val _ = new_constant("to_terminal",“:object -> arrow”)   

val ax1_1 = new_axiom("ax1_1",“∀X. tx∶ X → one ⇔ tx = to_terminal X”)

(*UTF8.chr 0x1D443 𝑃 *)

val _ = new_constant("zero",“:object”)

val _ = new_constant("from_initial",“:object -> arrow”)       

val ax1_2 = new_axiom("ax1_2",“∀X. ix∶ zero → X ⇔ ix = from_initial X”)


val _ = new_constant("po",“:object -> object -> object”)

val _ = set_mapped_fixity {fixity = Infix (NONASSOC,450),
                   term_name = "po",
                   tok = "×"};

    
val _ = new_constant("pa",“:arrow -> arrow -> arrow”)

val _ = new_constant("p1",“:object -> object -> arrow”)

val _ = new_constant("p2",“:object -> object -> arrow”)            

val ax1_3 = new_axiom("ax1_3",
                      “∀A B. (p1 A B) ∶ (po A B) → A ∧
                             (p2 A B) ∶ (po A B) → B ∧
                             ∀X f g. f∶ X → A ∧ g∶ X → B ⇒
                                     ∀fg. (fg∶ X → (po A B) ∧
                                           (p1 A B) o fg = f ∧
                                           (p2 A B) o fg = g) ⇔
                                          fg = pa f g”)  


val _ = new_constant("copo",“:object -> object -> object”)
Overload "+" = ``copo``
val _ = new_constant("copa",“:arrow -> arrow -> arrow”)

val _ = new_constant("i1",“:object -> object -> arrow”)

val _ = new_constant("i2",“:object -> object -> arrow”)            

val ax1_4 = new_axiom("ax1_4",
                      “∀A B. (i1 A B) ∶ A → (copo A B) ∧
                             (i2 A B) ∶ B → (copo A B)∧
                             ∀X f g. f∶ A → X ∧ g∶ B → X ⇒
                                     ∀fg. (fg∶ (copo A B) → X ∧
                                           fg o (i1 A B) = f ∧
                                           fg o (i2 A B) = g) ⇔
                                          fg = copa f g”)  
                                          


val _ = new_constant("eqo",“:arrow -> arrow -> object”)

val _ = new_constant("eqa",“:arrow -> arrow -> arrow”)

val _ = new_constant("eq_induce",“:arrow -> arrow -> arrow -> arrow”)
    

val ax1_5 = new_axiom("ax1_5",
                      “∀A B f g. f∶ A → B ∧ g∶ A → B ⇒
                                 (eqa f g)∶ (eqo f g) → A ∧
                                 f o (eqa f g) = g o eqa f g ∧
                                 ∀X h. h∶ X → A ∧
                                       f o h = g o h ⇒
                                       !x0. (x0∶ X → (eqo f g) ∧
                                             (eqa f g) o x0 = h) ⇔
                                            x0 = eq_induce f g h”)

                                                                         val _ = new_constant("coeqo",“:arrow -> arrow -> object”)

val _ = new_constant("coeqa",“:arrow -> arrow -> arrow”)

val _ = new_constant("coeq_induce",“:arrow -> arrow -> arrow -> arrow”)
    

val ax1_5 = new_axiom("ax1_6",
                      “∀A B f g. f∶ A → B ∧ g∶ A → B ⇒
                                 (eqa f g)∶ B → (coeqo f g) ∧
                                 (coeqa f g) o f = (coeqa f g) o g ∧
                                 ∀X h. h∶ B → X ∧
                                       h o f = h o g ⇒
                                       !x0. (x0∶ (coeqo f g) → X ∧
                                             x0 o (coeqa f g) = h) ⇔
                                            x0 = coeq_induce f g h”)


                                                                           
(*ax2 exponential*)

val _ = new_constant("exp",“:object -> object -> object”)

val _ = new_constant("ev",“:object -> object -> arrow”)

val _ = new_constant("tp",“:arrow -> arrow”)

(*A * B -> C    A -> B^C*)    

  

val ax2 = new_axiom("ax2",
                    “∀A B. (ev A B)∶ (po A (exp A B)) → B ∧
                        ∀X f. f∶ (po A X) → B ⇒
                           (∀h. (h∶ X → (exp A B) ∧
                                (ev A B) o
                                (pa (p1 A X) (h o (p2 A X))) = f) ⇔
                                h = tp f) ”)    

      
(*ax3 NNO*)

val _ = new_constant("N",“:object”)

val _ = new_constant("z",“:arrow”)

val _ = new_constant("s",“:arrow”)

val _ = new_constant("N_induce",“:arrow -> arrow -> arrow”)    
 
val ax3 = new_axiom("ax3",
                   “z∶ one → N ∧ s∶ N → N ∧
                   ∀X x0 t. x0∶ one → X ∧ t∶ X → X ⇒
                     !x. (x∶ N → X ∧ x o z = x0 ∧ x o s = t o x) ⇔
                         x = N_induce x0 t”)    
      

(*ax4 f ≠ g ⇒ ∃a. a ∈ A ∧ f a ≠ g a*)

(* a ∈ A if a∶ 1 ---> A ===== f ,g ===> B*)

val ax4 = new_axiom("ax4",
                   “∀A B f g. f∶ A → B ∧ g∶ A → B ∧ f ≠ g ⇒
                            ∃a. a∶ one → A ∧ f o a ≠ g o a
                    ”)    


(*ax5 if dom f has elements, then ∃g. such that fgf = f*)

val ax5 = new_axiom("ax5",
                   “∀A B f a. f∶ A → B ∧ a∶ one → A ⇒
                            ∃g. g∶ B → A ∧ f o g o f = f”)
      

(*ax6 every object other than 0 has elements*)

Definition is_iso_def:
is_iso f ⇔ (∃f'. dom f' = cod f ∧ cod f' = dom f ∧ f o f' = id (cod f) ∧ f' o f = id (dom f))
End

        
Definition are_iso_def:
are_iso A B ⇔ ∃f g. f∶ A → B ∧ g∶ B → A ∧
                    f o g = id B ∧ g o f = id A
End

val _ = set_mapped_fixity {fixity = Infix (NONASSOC,450),
                   term_name = "are_iso",
                   tok = "≅"};
  
val ax6 = new_axiom("ax6",
                   “∀X. ¬(X ≅ zero) ⇒ ∃x. x∶ one → X”)      

(*ax7 element of a sum is a member of one of the injection*)

Definition is_mono_def:   
  is_mono f ⇔
  ∀g1 g2. dom g1 = dom g2 ∧ cod g1 = dom f ∧ cod g2 = dom f ∧
          f o g1 = f o g2 ⇒ g1 = g2
End            


Definition is_mem:
is_mem x a ⇔ x∶ one → cod a ∧ is_mono a ∧
             ∃x0. x0∶ one → dom a ∧ a o x0 = x
End             

val ax7 = new_axiom("ax7",
                   “∀x A B. x∶ one → copo A B ⇒
                            (is_mem x (i1 A B) ∨ is_mem x (i2 A B))”)

(*ax8 there exists an object with more than one element*)                             
                   
val ax8 = new_axiom("ax8",
                   “∃X x1 x2. x1∶ one → X ∧ x2∶ one → X ∧ x1 ≠ x2”)
                                        

(*shortcut key for inserting Unicode*)
