theory flash112Rev imports flashPub
begin
section{*Main defintions*}
lemma NI_FAckVsInv112:  
    (*Rule0VsPInv0*)
  
  shows  "invHoldForRule' s (inv112 ) (NI_FAck ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

   
      by( auto)
 
  lemma NI_InvVsInv112:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv112 ) (NI_Inv  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_InvAck_1VsInv112:  
    (*Rule2VsPInv0*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iRule1~=iRule2  " 

  shows  "invHoldForRule' s (inv112 ) (NI_InvAck_1  iRule1  iRule2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_InvAck_1_HomeVsInv112:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv112 ) (NI_InvAck_1_Home  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_InvAck_2VsInv112:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv112 ) (NI_InvAck_2 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_GetX_GetXVsInv112:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv112 ) (NI_Local_GetX_GetX  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_GetX_Nak1VsInv112:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv112 ) (NI_Local_GetX_Nak1  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_GetX_Nak2VsInv112:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv112 ) (NI_Local_GetX_Nak2  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_GetX_Nak3VsInv112:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv112 ) (NI_Local_GetX_Nak3  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_GetX_PutX1VsInv112:  
  (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv112 ) (NI_Local_GetX_PutX1 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

  
      have "?P1 s"
         
        apply(cut_tac  a1 , auto)

         
        done

        then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

       by blast

  


 qed
lemma NI_Local_GetX_PutX2VsInv112:  
  (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv112 ) (NI_Local_GetX_PutX2 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

  
      have "?P1 s"
         
        apply(cut_tac  a1 , auto)

         
        done

        then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

       by blast

  


 qed
lemma NI_Local_GetX_PutX3VsInv112:  
  (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv112 ) (NI_Local_GetX_PutX3 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

  
      have "?P1 s"
         
        apply(cut_tac  a1 , auto)

         
        done

        then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

       by blast

  


 qed
lemma NI_Local_GetX_PutX4VsInv112:  
  (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv112 ) (NI_Local_GetX_PutX4 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

  
      have "?P1 s"
         
        apply(cut_tac  a1 , auto)

         
        done

        then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

       by blast

  


 qed
lemma NI_Local_GetX_PutX5VsInv112:  
  (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv112 ) (NI_Local_GetX_PutX5 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

  
      have "?P1 s"
         
        apply(cut_tac  a1 , auto)

         
        done

        then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

       by blast

  


 qed
lemma NI_Local_GetX_PutX6VsInv112:  
  (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv112 ) (NI_Local_GetX_PutX6 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

  
      have "?P1 s"
         
        apply(cut_tac  a1 , auto)

         
        done

        then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

       by blast

  


 qed
lemma NI_Local_GetX_PutX7VsInv112:  
  (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv112 ) (NI_Local_GetX_PutX7 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

  
      have "?P1 s"
         
        apply(cut_tac  a1 , auto)

         
        done

        then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

       by blast

  


 qed
lemma NI_Local_GetX_PutX8VsInv112:  
  (*Rule2VsPInv0*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iRule1~=iRule2  " 

  shows  "invHoldForRule' s (inv112 ) (NI_Local_GetX_PutX8 N  iRule1  iRule2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3 , auto)

         
        done

        then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

       by blast

  


 qed
lemma NI_Local_GetX_PutX8_homeVsInv112:  
  (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv112 ) (NI_Local_GetX_PutX8_home N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

  
      have "?P1 s"
         
        apply(cut_tac  a1 , auto)

         
        done

        then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

       by blast

  


 qed
lemma NI_Local_GetX_PutX9VsInv112:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv112 ) (NI_Local_GetX_PutX9 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_GetX_PutX10VsInv112:  
    (*Rule2VsPInv0*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iRule1~=iRule2  " 

  shows  "invHoldForRule' s (inv112 ) (NI_Local_GetX_PutX10 N  iRule1  iRule2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_GetX_PutX10_homeVsInv112:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv112 ) (NI_Local_GetX_PutX10_home N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_GetX_PutX11VsInv112:  
  (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv112 ) (NI_Local_GetX_PutX11 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

  
      have "?P1 s"
         
        apply(cut_tac  a1 , auto)

         
        done

        then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

       by blast

  


 qed
lemma NI_Local_Get_GetVsInv112:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv112 ) (NI_Local_Get_Get  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_Get_Nak1VsInv112:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv112 ) (NI_Local_Get_Nak1  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_Get_Nak2VsInv112:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv112 ) (NI_Local_Get_Nak2  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_Get_Nak3VsInv112:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv112 ) (NI_Local_Get_Nak3  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_Get_Put1VsInv112:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv112 ) (NI_Local_Get_Put1 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_Get_Put2VsInv112:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv112 ) (NI_Local_Get_Put2  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_Get_Put3VsInv112:  
  (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv112 ) (NI_Local_Get_Put3  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

  
      have "?P1 s"
         
        apply(cut_tac  a1 , auto)

         
        done

        then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

       by blast

  


 qed
lemma NI_Local_PutVsInv112:  
  (*Rule0VsPInv0*)
  shows  "invHoldForRule' s (inv112 ) (NI_Local_Put ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -

     have allCases:"formEval  ( andForm ( eqn ( IVar ( Para ''InvMarked'' Home) )  ( Const true ))    ( eqn ( IVar ( Para ''InvMarked'' Home) )  ( Const true ))  )  s  \<or>formEval  ( andForm ( eqn ( IVar ( Para ''InvMarked'' Home) )  ( Const true ))     (neg ( eqn ( IVar ( Para ''InvMarked'' Home) )  ( Const true )) )  )  s  \<or>formEval  ( andForm  (neg ( eqn ( IVar ( Para ''InvMarked'' Home) )  ( Const true )) )    ( eqn ( IVar ( Para ''InvMarked'' Home) )  ( Const true ))  )  s  \<or>formEval  ( andForm  (neg ( eqn ( IVar ( Para ''InvMarked'' Home) )  ( Const true )) )     (neg ( eqn ( IVar ( Para ''InvMarked'' Home) )  ( Const true )) )  )  s  "  
	                      by auto 

    moreover
                       {assume b1:"formEval ( andForm ( eqn ( IVar ( Para ''InvMarked'' Home) )  ( Const true ))    ( eqn ( IVar ( Para ''InvMarked'' Home) )  ( Const true ))  )  s"

      have "?P1 s"
         
        apply(cut_tac  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast
    }

    moreover
                       {assume b1:"formEval ( andForm ( eqn ( IVar ( Para ''InvMarked'' Home) )  ( Const true ))     (neg ( eqn ( IVar ( Para ''InvMarked'' Home) )  ( Const true )) )  )  s"

      have "?P1 s"
         
        apply(cut_tac  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast
    }

    moreover
                       {assume b1:"formEval ( andForm  (neg ( eqn ( IVar ( Para ''InvMarked'' Home) )  ( Const true )) )    ( eqn ( IVar ( Para ''InvMarked'' Home) )  ( Const true ))  )  s"

      have "?P1 s"
         
        apply(cut_tac  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast
    }

    moreover
                       {assume b1:"formEval ( andForm  (neg ( eqn ( IVar ( Para ''InvMarked'' Home) )  ( Const true )) )     (neg ( eqn ( IVar ( Para ''InvMarked'' Home) )  ( Const true )) )  )  s"

      have "?P1 s"
         
        apply(cut_tac  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast
    }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_PutXAcksDoneVsInv112:  
  (*Rule0VsPInv0*)
  shows  "invHoldForRule' s (inv112 ) (NI_Local_PutXAcksDone ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -

  
      have "?P1 s"
         
        apply( auto)

         
        done

        then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

       by blast

  


 qed
lemma NI_NakVsInv112:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv112 ) (NI_Nak  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Nak_ClearVsInv112:  
    (*Rule0VsPInv0*)
  
  shows  "invHoldForRule' s (inv112 ) (NI_Nak_Clear ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

   
      by( auto)
 
  lemma NI_Nak_HomeVsInv112:  
    (*Rule0VsPInv0*)
  
  shows  "invHoldForRule' s (inv112 ) (NI_Nak_Home ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

   
      by( auto)
 
  lemma NI_Remote_GetX_NakVsInv112:  
    (*Rule2VsPInv0*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iRule1~=iRule2  " 

  shows  "invHoldForRule' s (inv112 ) (NI_Remote_GetX_Nak  iRule1  iRule2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Remote_GetX_Nak_HomeVsInv112:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv112 ) (NI_Remote_GetX_Nak_Home  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Remote_GetX_PutXVsInv112:  
    (*Rule2VsPInv0*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iRule1~=iRule2  " 

  shows  "invHoldForRule' s (inv112 ) (NI_Remote_GetX_PutX  iRule1  iRule2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Remote_GetX_PutX_HomeVsInv112:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv112 ) (NI_Remote_GetX_PutX_Home  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Remote_Get_Nak1VsInv112:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv112 ) (NI_Remote_Get_Nak1  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Remote_Get_Nak2VsInv112:  
    (*Rule2VsPInv0*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iRule1~=iRule2  " 

  shows  "invHoldForRule' s (inv112 ) (NI_Remote_Get_Nak2  iRule1  iRule2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Remote_Get_Put1VsInv112:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv112 ) (NI_Remote_Get_Put1  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Remote_Get_Put2VsInv112:  
    (*Rule2VsPInv0*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iRule1~=iRule2  " 

  shows  "invHoldForRule' s (inv112 ) (NI_Remote_Get_Put2  iRule1  iRule2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Remote_PutVsInv112:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv112 ) (NI_Remote_Put  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Remote_PutXVsInv112:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv112 ) (NI_Remote_PutX  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_ReplaceVsInv112:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv112 ) (NI_Replace  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_ReplaceHomeVsInv112:  
    (*Rule0VsPInv0*)
  
  shows  "invHoldForRule' s (inv112 ) (NI_ReplaceHome ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

   
      by( auto)
 
  lemma NI_ReplaceHomeShrVldVsInv112:  
    (*Rule0VsPInv0*)
  
  shows  "invHoldForRule' s (inv112 ) (NI_ReplaceHomeShrVld ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

   
      by( auto)
 
  lemma NI_ReplaceShrVldVsInv112:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv112 ) (NI_ReplaceShrVld  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_ShWbVsInv112:  
    (*Rule0VsPInv0*)
  
  shows  "invHoldForRule' s (inv112 ) (NI_ShWb N ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

   
      by( auto)
 
  lemma NI_WbVsInv112:  
    (*Rule0VsPInv0*)
  
  shows  "invHoldForRule' s (inv112 ) (NI_Wb ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

   
      by( auto)
 
  lemma PI_Local_GetX_GetX1VsInv112:  
    (*Rule0VsPInv0*)
  
  shows  "invHoldForRule' s (inv112 ) (PI_Local_GetX_GetX1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

   
      by( auto)
 
  lemma PI_Local_GetX_GetX2VsInv112:  
    (*Rule0VsPInv0*)
  
  shows  "invHoldForRule' s (inv112 ) (PI_Local_GetX_GetX2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

   
      by( auto)
 
  lemma PI_Local_GetX_PutX1VsInv112:  
  (*Rule0VsPInv0*)
  shows  "invHoldForRule' s (inv112 ) (PI_Local_GetX_PutX1 N ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -

  
      have "?P1 s"
         
        apply( auto)

         
        done

        then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

       by blast

  


 qed
lemma PI_Local_GetX_PutX2VsInv112:  
  (*Rule0VsPInv0*)
  shows  "invHoldForRule' s (inv112 ) (PI_Local_GetX_PutX2 N ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -

  
      have "?P1 s"
         
        apply( auto)

         
        done

        then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

       by blast

  


 qed
lemma PI_Local_GetX_PutX3VsInv112:  
  (*Rule0VsPInv0*)
  shows  "invHoldForRule' s (inv112 ) (PI_Local_GetX_PutX3 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -

  
      have "?P1 s"
         
        apply( auto)

         
        done

        then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

       by blast

  


 qed
lemma PI_Local_GetX_PutX4VsInv112:  
  (*Rule0VsPInv0*)
  shows  "invHoldForRule' s (inv112 ) (PI_Local_GetX_PutX4 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -

  
      have "?P1 s"
         
        apply( auto)

         
        done

        then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

       by blast

  


 qed
lemma PI_Local_Get_GetVsInv112:  
    (*Rule0VsPInv0*)
  
  shows  "invHoldForRule' s (inv112 ) (PI_Local_Get_Get ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

   
      by( auto)
 
  lemma PI_Local_Get_PutVsInv112:  
  (*Rule0VsPInv0*)
  shows  "invHoldForRule' s (inv112 ) (PI_Local_Get_Put ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -

     have allCases:"formEval  ( andForm ( eqn ( IVar ( Para ''InvMarked'' Home) )  ( Const true ))    ( eqn ( IVar ( Para ''InvMarked'' Home) )  ( Const true ))  )  s  \<or>formEval  ( andForm ( eqn ( IVar ( Para ''InvMarked'' Home) )  ( Const true ))     (neg ( eqn ( IVar ( Para ''InvMarked'' Home) )  ( Const true )) )  )  s  \<or>formEval  ( andForm  (neg ( eqn ( IVar ( Para ''InvMarked'' Home) )  ( Const true )) )    ( eqn ( IVar ( Para ''InvMarked'' Home) )  ( Const true ))  )  s  \<or>formEval  ( andForm  (neg ( eqn ( IVar ( Para ''InvMarked'' Home) )  ( Const true )) )     (neg ( eqn ( IVar ( Para ''InvMarked'' Home) )  ( Const true )) )  )  s  "  
	                      by auto 

    moreover
                       {assume b1:"formEval ( andForm ( eqn ( IVar ( Para ''InvMarked'' Home) )  ( Const true ))    ( eqn ( IVar ( Para ''InvMarked'' Home) )  ( Const true ))  )  s"

      have "?P1 s"
         
        apply(cut_tac  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast
    }

    moreover
                       {assume b1:"formEval ( andForm ( eqn ( IVar ( Para ''InvMarked'' Home) )  ( Const true ))     (neg ( eqn ( IVar ( Para ''InvMarked'' Home) )  ( Const true )) )  )  s"

      have "?P1 s"
         
        apply(cut_tac  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast
    }

    moreover
                       {assume b1:"formEval ( andForm  (neg ( eqn ( IVar ( Para ''InvMarked'' Home) )  ( Const true )) )    ( eqn ( IVar ( Para ''InvMarked'' Home) )  ( Const true ))  )  s"

      have "?P1 s"
         
        apply(cut_tac  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast
    }

    moreover
                       {assume b1:"formEval ( andForm  (neg ( eqn ( IVar ( Para ''InvMarked'' Home) )  ( Const true )) )     (neg ( eqn ( IVar ( Para ''InvMarked'' Home) )  ( Const true )) )  )  s"

      have "?P1 s"
         
        apply(cut_tac  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast
    }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma PI_Local_PutXVsInv112:  
  (*Rule0VsPInv0*)
  shows  "invHoldForRule' s (inv112 ) (PI_Local_PutX ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -

  
      have "?P1 s"
         
        apply( auto)

         
        done

        then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

       by blast

  


 qed
lemma PI_Local_ReplaceVsInv112:  
  (*Rule0VsPInv0*)
  shows  "invHoldForRule' s (inv112 ) (PI_Local_Replace ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -

  
      have "?P1 s"
         
        apply( auto)

         
        done

        then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

       by blast

  


 qed
lemma PI_Remote_GetVsInv112:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv112 ) (PI_Remote_Get  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma PI_Remote_GetXVsInv112:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv112 ) (PI_Remote_GetX  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma PI_Remote_PutXVsInv112:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv112 ) (PI_Remote_PutX  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma PI_Remote_ReplaceVsInv112:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv112 ) (PI_Remote_Replace  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma StoreVsInv112:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv112 ) (Store  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma StoreHomeVsInv112:  
    (*Rule0VsPInv0*)
  
  shows  "invHoldForRule' s (inv112 ) (StoreHome ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

   
      by( auto)
 
  end
