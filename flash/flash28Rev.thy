theory flash28Rev imports flashPub
begin
section{*Main defintions*}
lemma NI_FAckVsInv28:  
    (*Rule0VsPInv1*)
  assumes   a1:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv28  iInv1 ) (NI_FAck ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by (cut_tac  a1 , auto)
 lemma NI_InvVsInv28:  
  (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv28  iInv1 ) (NI_Inv  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>((iRule1~=iInv1 ))   "  
	                      by( cut_tac  a1  a2  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_InvAck_1VsInv28:  
    (*Rule2VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iInv1 \<le> N" and  a4:"iRule1~=iRule2  " 

  shows  "invHoldForRule' s (inv28  iInv1 ) (NI_InvAck_1  iRule1  iRule2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by(cut_tac a1 a2 a3 a4, auto) 
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto 
 qed
  lemma NI_InvAck_1_HomeVsInv28:  
    (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv28  iInv1 ) (NI_InvAck_1_Home  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by  (cut_tac  a1  a2 , auto)
 lemma NI_InvAck_2VsInv28:  
    (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv28  iInv1 ) (NI_InvAck_2 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by  (cut_tac  a1  a2 , auto)
 lemma NI_Local_GetX_GetXVsInv28:  
    (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv28  iInv1 ) (NI_Local_GetX_GetX  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by  (cut_tac  a1  a2 , auto)
 lemma NI_Local_GetX_Nak1VsInv28:  
    (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv28  iInv1 ) (NI_Local_GetX_Nak1  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by  (cut_tac  a1  a2 , auto)
 lemma NI_Local_GetX_Nak2VsInv28:  
    (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv28  iInv1 ) (NI_Local_GetX_Nak2  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by  (cut_tac  a1  a2 , auto)
 lemma NI_Local_GetX_Nak3VsInv28:  
    (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv28  iInv1 ) (NI_Local_GetX_Nak3  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by  (cut_tac  a1  a2 , auto)
 lemma NI_Local_GetX_PutX1VsInv28:  
    (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv28  iInv1 ) (NI_Local_GetX_PutX1 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by  (cut_tac  a1  a2 , auto)
 lemma NI_Local_GetX_PutX2VsInv28:  
    (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv28  iInv1 ) (NI_Local_GetX_PutX2 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by  (cut_tac  a1  a2 , auto)
 lemma NI_Local_GetX_PutX3VsInv28:  
    (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv28  iInv1 ) (NI_Local_GetX_PutX3 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by  (cut_tac  a1  a2 , auto)
 lemma NI_Local_GetX_PutX4VsInv28:  
    (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv28  iInv1 ) (NI_Local_GetX_PutX4 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by  (cut_tac  a1  a2 , auto)
 lemma NI_Local_GetX_PutX5VsInv28:  
    (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv28  iInv1 ) (NI_Local_GetX_PutX5 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by  (cut_tac  a1  a2 , auto)
 lemma NI_Local_GetX_PutX6VsInv28:  
    (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv28  iInv1 ) (NI_Local_GetX_PutX6 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by  (cut_tac  a1  a2 , auto)
 lemma NI_Local_GetX_PutX7VsInv28:  
    (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv28  iInv1 ) (NI_Local_GetX_PutX7 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by  (cut_tac  a1  a2 , auto)
 lemma NI_Local_GetX_PutX8VsInv28:  
    (*Rule2VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iInv1 \<le> N" and  a4:"iRule1~=iRule2  " 

  shows  "invHoldForRule' s (inv28  iInv1 ) (NI_Local_GetX_PutX8 N  iRule1  iRule2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by(cut_tac a1 a2 a3 a4, auto) 
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto 
 qed
  lemma NI_Local_GetX_PutX8_homeVsInv28:  
    (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv28  iInv1 ) (NI_Local_GetX_PutX8_home N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by  (cut_tac  a1  a2 , auto)
 lemma NI_Local_GetX_PutX9VsInv28:  
    (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv28  iInv1 ) (NI_Local_GetX_PutX9 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by  (cut_tac  a1  a2 , auto)
 lemma NI_Local_GetX_PutX10VsInv28:  
    (*Rule2VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iInv1 \<le> N" and  a4:"iRule1~=iRule2  " 

  shows  "invHoldForRule' s (inv28  iInv1 ) (NI_Local_GetX_PutX10 N  iRule1  iRule2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by(cut_tac a1 a2 a3 a4, auto) 
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto 
 qed
  lemma NI_Local_GetX_PutX10_homeVsInv28:  
    (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv28  iInv1 ) (NI_Local_GetX_PutX10_home N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by  (cut_tac  a1  a2 , auto)
 lemma NI_Local_GetX_PutX11VsInv28:  
    (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv28  iInv1 ) (NI_Local_GetX_PutX11 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by  (cut_tac  a1  a2 , auto)
 lemma NI_Local_Get_GetVsInv28:  
    (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv28  iInv1 ) (NI_Local_Get_Get  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by  (cut_tac  a1  a2 , auto)
 lemma NI_Local_Get_Nak1VsInv28:  
    (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv28  iInv1 ) (NI_Local_Get_Nak1  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by  (cut_tac  a1  a2 , auto)
 lemma NI_Local_Get_Nak2VsInv28:  
    (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv28  iInv1 ) (NI_Local_Get_Nak2  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by  (cut_tac  a1  a2 , auto)
 lemma NI_Local_Get_Nak3VsInv28:  
    (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv28  iInv1 ) (NI_Local_Get_Nak3  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by  (cut_tac  a1  a2 , auto)
 lemma NI_Local_Get_Put1VsInv28:  
    (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv28  iInv1 ) (NI_Local_Get_Put1 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by  (cut_tac  a1  a2 , auto)
 lemma NI_Local_Get_Put2VsInv28:  
    (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv28  iInv1 ) (NI_Local_Get_Put2  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by  (cut_tac  a1  a2 , auto)
 lemma NI_Local_Get_Put3VsInv28:  
    (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv28  iInv1 ) (NI_Local_Get_Put3  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by  (cut_tac  a1  a2 , auto)
 lemma NI_Local_PutVsInv28:  
  (*Rule0VsPInv1*)
  assumes   a1:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv28  iInv1 ) (NI_Local_Put ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 

  
      have "?P1 s"
         
        apply(cut_tac  a1 , auto)

         
        done

        then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

       by blast

  


 qed
lemma NI_Local_PutXAcksDoneVsInv28:  
  (*Rule0VsPInv1*)
  assumes   a1:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv28  iInv1 ) (NI_Local_PutXAcksDone ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 

  
      have "?P1 s"
         
        apply(cut_tac  a1 , auto)

         
        done

        then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

       by blast

  


 qed
lemma NI_NakVsInv28:  
    (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv28  iInv1 ) (NI_Nak  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by  (cut_tac  a1  a2 , auto)
 lemma NI_Nak_ClearVsInv28:  
    (*Rule0VsPInv1*)
  assumes   a1:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv28  iInv1 ) (NI_Nak_Clear ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by (cut_tac  a1 , auto)
 lemma NI_Nak_HomeVsInv28:  
  (*Rule0VsPInv1*)
  assumes   a1:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv28  iInv1 ) (NI_Nak_Home ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 

  
      have "?P1 s"
         
        apply(cut_tac  a1 , auto)

         
        done

        then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

       by blast

  


 qed
lemma NI_Remote_GetX_NakVsInv28:  
    (*Rule2VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iInv1 \<le> N" and  a4:"iRule1~=iRule2  " 

  shows  "invHoldForRule' s (inv28  iInv1 ) (NI_Remote_GetX_Nak  iRule1  iRule2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by(cut_tac a1 a2 a3 a4, auto) 
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto 
 qed
  lemma NI_Remote_GetX_Nak_HomeVsInv28:  
  (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv28  iInv1 ) (NI_Remote_GetX_Nak_Home  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>((iRule1~=iInv1 ))   "  
	                      by( cut_tac  a1  a2  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 ))"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Remote_GetX_PutXVsInv28:  
    (*Rule2VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iInv1 \<le> N" and  a4:"iRule1~=iRule2  " 

  shows  "invHoldForRule' s (inv28  iInv1 ) (NI_Remote_GetX_PutX  iRule1  iRule2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1\<and>(iRule2~=iInv1 ))   \<or>((iRule1~=iInv1 )\<and>iRule2=iInv1)   \<or>((iRule1~=iInv1 )\<and>(iRule2~=iInv1 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  , auto) 
moreover
                {assume b1:"(iRule1=iInv1\<and>(iRule2~=iInv1 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 )\<and>iRule2=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 )\<and>(iRule2~=iInv1 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Remote_GetX_PutX_HomeVsInv28:  
  (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv28  iInv1 ) (NI_Remote_GetX_PutX_Home  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>((iRule1~=iInv1 ))   "  
	                      by( cut_tac  a1  a2  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 ))"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Remote_Get_Nak1VsInv28:  
  (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv28  iInv1 ) (NI_Remote_Get_Nak1  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>((iRule1~=iInv1 ))   "  
	                      by( cut_tac  a1  a2  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 ))"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Remote_Get_Nak2VsInv28:  
    (*Rule2VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iInv1 \<le> N" and  a4:"iRule1~=iRule2  " 

  shows  "invHoldForRule' s (inv28  iInv1 ) (NI_Remote_Get_Nak2  iRule1  iRule2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by(cut_tac a1 a2 a3 a4, auto) 
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto 
 qed
  lemma NI_Remote_Get_Put1VsInv28:  
  (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv28  iInv1 ) (NI_Remote_Get_Put1  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>((iRule1~=iInv1 ))   "  
	                      by( cut_tac  a1  a2  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 ))"

                  
      have "?P3 s"

         
        apply(   cut_tac  a1  a2  b1 , simp)

        apply(rule_tac x=" (neg ( andForm ( eqn ( IVar ( Para ''CacheState'' iRule1) )  ( Const CACHE_E ))    ( eqn ( IVar ( Para ''CacheState'' iInv1) )  ( Const CACHE_E ))  ) ) " in exI,auto)
 
        
        done

       
       then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Remote_Get_Put2VsInv28:  
    (*Rule2VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iInv1 \<le> N" and  a4:"iRule1~=iRule2  " 

  shows  "invHoldForRule' s (inv28  iInv1 ) (NI_Remote_Get_Put2  iRule1  iRule2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1\<and>(iRule2~=iInv1 ))   \<or>((iRule1~=iInv1 )\<and>iRule2=iInv1)   \<or>((iRule1~=iInv1 )\<and>(iRule2~=iInv1 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  , auto) 
moreover
                {assume b1:"(iRule1=iInv1\<and>(iRule2~=iInv1 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 )\<and>iRule2=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 )\<and>(iRule2~=iInv1 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Remote_PutVsInv28:  
  (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv28  iInv1 ) (NI_Remote_Put  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>((iRule1~=iInv1 ))   "  
	                      by( cut_tac  a1  a2  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                     have allCases:"formEval  ( eqn ( IVar ( Para ''InvMarked'' iInv1) )  ( Const true ))  s  \<or>formEval   (neg ( eqn ( IVar ( Para ''InvMarked'' iInv1) )  ( Const true )) )  s  "  
	                      by auto 

    moreover
                       {assume c1:"formEval ( eqn ( IVar ( Para ''InvMarked'' iInv1) )  ( Const true ))  s"

      have "?P1 s"
         
        apply(cut_tac  a1  a2  b1  c1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast
    }

    moreover
                       {assume c1:"formEval  (neg ( eqn ( IVar ( Para ''InvMarked'' iInv1) )  ( Const true )) )  s"

      have "?P1 s"
         
        apply(cut_tac  a1  a2  b1  c1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast
    }
   ultimately have "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     

	                }
moreover
                {assume b1:"((iRule1~=iInv1 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Remote_PutXVsInv28:  
  (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv28  iInv1 ) (NI_Remote_PutX  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>((iRule1~=iInv1 ))   "  
	                      by( cut_tac  a1  a2  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P3 s"

         
        apply(   cut_tac  a1  a2  b1 , simp)

        apply(rule_tac x=" (neg ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' Home) )  ( Const UNI_Put ))    ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_PutX ))  ) ) " in exI,auto)
 
        
        done

       
       then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_ReplaceVsInv28:  
    (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv28  iInv1 ) (NI_Replace  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by  (cut_tac  a1  a2 , auto)
 lemma NI_ReplaceHomeVsInv28:  
    (*Rule0VsPInv1*)
  assumes   a1:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv28  iInv1 ) (NI_ReplaceHome ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by (cut_tac  a1 , auto)
 lemma NI_ReplaceHomeShrVldVsInv28:  
    (*Rule0VsPInv1*)
  assumes   a1:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv28  iInv1 ) (NI_ReplaceHomeShrVld ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by (cut_tac  a1 , auto)
 lemma NI_ReplaceShrVldVsInv28:  
    (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv28  iInv1 ) (NI_ReplaceShrVld  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by  (cut_tac  a1  a2 , auto)
 lemma NI_ShWbVsInv28:  
    (*Rule0VsPInv1*)
  assumes   a1:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv28  iInv1 ) (NI_ShWb N ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by (cut_tac  a1 , auto)
 lemma NI_WbVsInv28:  
    (*Rule0VsPInv1*)
  assumes   a1:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv28  iInv1 ) (NI_Wb ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by (cut_tac  a1 , auto)
 lemma PI_Local_GetX_GetX1VsInv28:  
  (*Rule0VsPInv1*)
  assumes   a1:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv28  iInv1 ) (PI_Local_GetX_GetX1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 

  
      have "?P1 s"
         
        apply(cut_tac  a1 , auto)

         
        done

        then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

       by blast

  


 qed
lemma PI_Local_GetX_GetX2VsInv28:  
  (*Rule0VsPInv1*)
  assumes   a1:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv28  iInv1 ) (PI_Local_GetX_GetX2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 

  
      have "?P1 s"
         
        apply(cut_tac  a1 , auto)

         
        done

        then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

       by blast

  


 qed
lemma PI_Local_GetX_PutX1VsInv28:  
    (*Rule0VsPInv1*)
  assumes   a1:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv28  iInv1 ) (PI_Local_GetX_PutX1 N ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by (cut_tac  a1 , auto)
 lemma PI_Local_GetX_PutX2VsInv28:  
    (*Rule0VsPInv1*)
  assumes   a1:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv28  iInv1 ) (PI_Local_GetX_PutX2 N ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by (cut_tac  a1 , auto)
 lemma PI_Local_GetX_PutX3VsInv28:  
    (*Rule0VsPInv1*)
  assumes   a1:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv28  iInv1 ) (PI_Local_GetX_PutX3 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by (cut_tac  a1 , auto)
 lemma PI_Local_GetX_PutX4VsInv28:  
    (*Rule0VsPInv1*)
  assumes   a1:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv28  iInv1 ) (PI_Local_GetX_PutX4 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by (cut_tac  a1 , auto)
 lemma PI_Local_Get_GetVsInv28:  
  (*Rule0VsPInv1*)
  assumes   a1:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv28  iInv1 ) (PI_Local_Get_Get ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 

  
      have "?P1 s"
         
        apply(cut_tac  a1 , auto)

         
        done

        then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

       by blast

  


 qed
lemma PI_Local_Get_PutVsInv28:  
    (*Rule0VsPInv1*)
  assumes   a1:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv28  iInv1 ) (PI_Local_Get_Put ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by (cut_tac  a1 , auto)
 lemma PI_Local_PutXVsInv28:  
    (*Rule0VsPInv1*)
  assumes   a1:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv28  iInv1 ) (PI_Local_PutX ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by (cut_tac  a1 , auto)
 lemma PI_Local_ReplaceVsInv28:  
    (*Rule0VsPInv1*)
  assumes   a1:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv28  iInv1 ) (PI_Local_Replace ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by (cut_tac  a1 , auto)
 lemma PI_Remote_GetVsInv28:  
    (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv28  iInv1 ) (PI_Remote_Get  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by  (cut_tac  a1  a2 , auto)
 lemma PI_Remote_GetXVsInv28:  
    (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv28  iInv1 ) (PI_Remote_GetX  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by  (cut_tac  a1  a2 , auto)
 lemma PI_Remote_PutXVsInv28:  
  (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv28  iInv1 ) (PI_Remote_PutX  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>((iRule1~=iInv1 ))   "  
	                      by( cut_tac  a1  a2  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma PI_Remote_ReplaceVsInv28:  
    (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv28  iInv1 ) (PI_Remote_Replace  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by  (cut_tac  a1  a2 , auto)
 lemma StoreVsInv28:  
    (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv28  iInv1 ) (Store  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by  (cut_tac  a1  a2 , auto)
 lemma StoreHomeVsInv28:  
    (*Rule0VsPInv1*)
  assumes   a1:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv28  iInv1 ) (StoreHome ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by (cut_tac  a1 , auto)
 end
