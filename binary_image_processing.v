
Require Import Nat.
From Coq Require Import List Lia.
From Coq Require Import EqNat.
From Coq Require Import Arith.PeanoNat.
Import ListNotations.
Require Import Bool. 

(*Binary color*)
Inductive color: Type:=
 | white: color
 | black: color.

(*Pixel of binary images*)
Inductive pixel: Type :=
 | Pixel (r c: nat) (col: color).

Definition image := list pixel.

Notation "B{ r , c , col }" := (Pixel r c col).

Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Definition abinaryimage := 
      [B{0,0,black};B{0,1,white};B{0,2,white};B{0,3,black};
       B{1,0,black};B{1,1,black};B{1,2,white};B{1,3,black};
       B{2,0,black};B{2,1,white};B{2,2,black};B{2,3,black};
       B{3,0,black};B{3,1,white};B{3,2,white};B{3,3,black}].

(** These functions are defined to convert the Coq binary image to the real binary image **)
(*converts gray color to binary value*)
Definition graytonat (c: color) : nat :=
 match c with
 | white => 0
 | black => 1
 end. 

(*Real binary image with rows, colos and list of pixels*)
Record realimage :=
 make_rimage
 {
   rows: nat;
   cols: nat;
   pixels: list nat
 }.

(*gets the number of rows in the binary image*)
Fixpoint rowsinimage (img: image) (d: nat) : nat :=
  match img with
 | nil => d
 | B{r,c,g}::tl => if d <? r then rowsinimage tl r else rowsinimage tl d
 end.

(*gets the number of cols in the binary image*)
Fixpoint colsinimage (img: image) (d: nat) : nat :=
  match img with
 | nil => d
 | B{r,c,g}::tl => if d <? c then colsinimage tl c else colsinimage tl d
 end.

(*gets the list of pixels in the binary image*)
Fixpoint pixelsinimage (img: image): list nat :=
 match img with
 | nil => nil
 | B{r,c,g}::tl => cons (graytonat g) (pixelsinimage tl)
 end. 

(*converts Coq binary image to real binary image*)
Definition imagetorealimage (img: image) : realimage :=
 {|rows:= (rowsinimage img 0);
   cols:= (colsinimage img 0);
   pixels:= (pixelsinimage img)
  |}.

(*Example*)
 Compute (imagetorealimage abinaryimage).
(********************)



(*Pixel of grayscale image*)
Inductive gspixel: Type :=
 | GSPixel (r c v: nat). 

(*Gray scaleimage*)
Definition gsimage := list gspixel.

Notation "G{ r , c , v }" := (GSPixel r c v).

Fixpoint rev (l: list nat) : list nat :=
 match l with
 | nil => nil
 | h::tl => (rev tl)++[h]
 end.

(*Creates grayscale image (as defined in Coq) from the grayscal matrix image*)
Fixpoint createimage (matrix: list nat) (row: nat) (col: nat) (maxcol: nat): gsimage :=
 match matrix with 
 | nil => nil
 | cons gray m => 
      match row, col with
      | O, O => [G{row, col, gray}] 
      | S r, O => (createimage m r maxcol maxcol) ++ [G{row, col, gray}]
      | O, S c => (createimage m row c maxcol) ++ [G{row, col, gray}]
      | S r, S c => (createimage m row c maxcol) ++ [G{row, col, gray}]
      end 
 end.
 
(*
  3  4  8
  9  6  7

rev=> 7;6;9;8;4;3
Compute (createimage (rev [3;4;8;9;6;7]) (2-1) (3-1) (3-1)).
*)

(***********************************************************)
(**************** Functions on binary images ***************)
(***********************************************************)

Definition eqbcol (c1 c2: color) : bool :=
 match c1, c2 with
 | white, white => true
 | black, black => true
 | _, _ => false
 end.

Definition negcolor (c: color) : color :=
 match c with
 | white => black
 | black => white
 end.

Definition negpix (p: pixel) : pixel :=
 match p with
 | B{r,c,col} => B{r,c, negcolor col}
 end. 

Definition negimage (pic: image) : image := map negpix pic. 

Definition eqpixel (p1 p2: pixel) : bool :=
 match p1, p2 with
| B{r,c,col}, B{r',c',col'} => 
    andb (andb (r =? r')  (c =? c')) (eqbcol col col')
end.

Fixpoint negpiximg (p: pixel) (img: image) : image :=
 match img with
 | nil => nil
 | cons p' tl => if eqpixel p p' then
             cons (negpix p') (negpiximg p tl)
            else cons p' (negpiximg p tl)
 end.

(***********************************************************)
(**************** Functions on grayscale images ************)
(***********************************************************)

(*Thresholding*)
(*Note: In the tutorial images and definitions, 0 is white and 1 is black.*)
Fixpoint thresholding (img: gsimage) (thresh: nat) : image :=
 match img with
 | nil => nil
 | cons G{r,c,gsv} tl => if (gsv <=? thresh) 
                        then cons B{r,c,black} (thresholding tl thresh)
                        else cons B{r,c,white} (thresholding tl thresh)
 end.

(*Range of thresholds*)
Fixpoint thresholdrange (img: gsimage) (T1 T2: nat) : image :=
 match img with
 | nil => nil
 | G{r,c,gsv}::tl => if andb (T1 <=? gsv) (gsv <=? T2) 
                        then B{r,c,black}::(thresholdrange tl T1 T2)
                        else B{r,c,white}::(thresholdrange tl T1 T2)
 end.

(*Projections (area)*)
Fixpoint areasize (img:  image) : nat := 
 match img with
 | nil => 0
 | B{r,c,col}::tl => match col with
      | black => S (areasize tl) 
      | white => areasize tl
      end
 end.

(*runlength of white color only*)
Fixpoint runlenwhite (img: image) (l: list nat) : list nat :=
 match img, l with
 | nil, 0::tl'' => rev tl''
 | nil, _ => rev l
 | B{_,_,white}::tl', nil => runlenwhite tl' (1::nil)
 | B{_,_,white}::tl', h::tl'' => runlenwhite tl' (S h::tl'')
 | B{_,_,black}::tl', 0::tl'' => runlenwhite tl' l
 | B{_,_,black}::tl', _ => runlenwhite tl' (0::l)
 end.

(*runlength of black color only*)
Fixpoint runlenblack (img: image) (l: list nat) : list nat :=
 match img, l with
 | nil, 0::tl'' => rev tl''
 | nil, _ => rev l
 | B{_,_,black}::tl', nil => runlenblack tl' (1::nil)
 | B{_,_,black}::tl', h::tl'' => runlenblack tl' (S h::tl'')
 | B{_,_,white}::tl', 0::tl'' => runlenblack tl' l
 | B{_,_,white}::tl', _ => runlenblack tl' (0::l)
 end.

Compute (runlenblack abinaryimage nil).
Compute (runlenblack abinaryimage [1; 3; 2; 3; 1]).

Fixpoint alternate (l1 l2: list nat) : list nat :=
 match l1, l2 with
 | nil, _ => l2
 | _, nil => l1
 | h1::tl1, h2::tl2 => h1::h2::(alternate tl1 tl2)
 end. 

(*keeps runs of the color as they happen to be in the image.*)
Definition runlength (img: image) : list nat := 
 match img with
 | nil => nil
 | B{r,c,black}::tl' => alternate (runlenblack img nil) (runlenwhite img nil)
 | B{r,c,white}::tl' => alternate (runlenwhite img nil) (runlenblack img nil)
 end.

(*keeps 1 (black) runs first*)
Definition runlength' (img: image) : list nat := alternate (runlenblack img nil) (runlenwhite img nil).

Definition myimage := cons B{2,4,white} (cons B{2,4,black} (cons B{2,4,black} (cons B{2,4,black} (cons B{2,4,white} (cons B{2,5,white} nil))))).

Fixpoint sumrunlen (runl: list nat) : nat :=
 match runl with
 | nil => 0
 | r::tl => r + (sumrunlen tl)
 end. 


(********************************************************************)
(************** Axillary Lemmas *************************************)
(********************************************************************)

Lemma eqb_eq n m : eqb n m = true <-> n = m.
Proof.
 revert m.
 induction n; destruct m; simpl; rewrite ?IHn; split; try easy.
Qed.

Lemma leb_le n m : (n <=? m) = true <-> n <= m.
Proof.
 revert m.
 induction n; destruct m; simpl.
 - now split.
 - split; trivial. intro; apply Peano.le_0_n.
 - now split.
 - rewrite IHn. split.
   + apply Peano.le_n_S.
   + apply Peano.le_S_n.
Qed.

Lemma ltb_lt n m : (n <? m) = true <-> n < m.
Proof.
 apply leb_le.
Qed.

Lemma ltb_lt_not n m : (n <? m) = false <-> ~ n < m.
Proof.
 intros.  split.
 intros.  unfold Nat.ltb in H.
 simpl in H. destruct m.
 auto with arith. 
 apply Nat.leb_gt in H. lia.
 intros. unfold Nat.ltb. 
 simpl. destruct m.
 auto with arith. 
 apply Nat.leb_gt. 
 lia.
Qed.

Lemma negpix_involution: forall pix: pixel, negpix (negpix pix) = pix.
Proof. 
 intro.
 destruct pix.
 simpl. 
 induction col. 
 + simpl. auto.
 + simpl. auto.
Qed.  

Lemma negimg_involution: forall img: image, negimage (negimage img) = img.
Proof. 
 intros.
 induction img.
 + simpl. auto.
 + simpl. rewrite IHimg.
   rewrite negpix_involution.
   auto.
Qed.

(*Added *)
Lemma plus_n_o: forall n, n + O = n.
Proof.
  induction n.
 + simpl. auto.
 + simpl. rewrite IHn. auto.
Qed.

(*Added *)
Lemma plus_n_Sm: forall n m, S (n + m) = n + (S m).
 Proof. 
  intros.
  induction n.
  simpl.
  reflexivity.
  simpl.  
  rewrite IHn.
  reflexivity.
Qed.

(*Added *)
Lemma plus_comm: forall n m, n + m = m + n.
Proof.
 intros.
 induction n.
 simpl.
 rewrite plus_n_o.
 reflexivity.
 simpl.
 rewrite IHn.
 rewrite plus_n_Sm.
 reflexivity.
Qed.

Lemma plus_assoc: forall x y z, x + (y + z) = (x + y) + z. 
Proof. 
 intros.
 induction x as [ | x']. 
 + simpl. auto.
 + simpl. rewrite IHx'. auto.
Qed.


(*****************************************************************)
(************************ Run-lenth (page 28) ********************)
(*****************************************************************)

Lemma runlen_0_nil: forall img: image, runlenblack img [ ] = runlenblack img [0].
Proof. 
 intro.
 induction img.
 + simpl. auto. 
 + destruct a. 
   destruct col.
   - simpl. auto.
   - simpl. auto.
Qed.

(**Copied some script from CoqClub**)
Lemma sumrunlen_app_plus_distr : forall l l',
  sumrunlen (l ++ l') = sumrunlen l + sumrunlen l'.
Proof.
  induction l; simpl; intros; auto.
  rewrite IHl; lia.
Qed.

(*Added *)
Lemma sumrunlen_rev: forall ln, sumrunlen (rev ln) = sumrunlen ln. 
Proof.
 intro.
 induction ln.
 + simpl. auto.
 + simpl. rewrite sumrunlen_app_plus_distr.
   rewrite IHln. 
   simpl. 
   rewrite plus_n_o.
   rewrite plus_comm.
   auto.
Qed.

Lemma sumrunlen_l' : forall lb ln ln',
  sumrunlen (runlenblack lb (ln ++ ln')) =
  sumrunlen ln + sumrunlen (runlenblack lb ln').
Proof.
  induction lb; simpl; intros.
  - destruct ln, ln'; simpl; auto.
    + destruct n; rewrite app_nil_r; simpl; auto.
     (*added*)
      * rewrite sumrunlen_rev.
        rewrite plus_n_o.
        auto.
      * rewrite sumrunlen_app_plus_distr.
        rewrite plus_n_o.
        rewrite sumrunlen_rev.
        simpl.
        rewrite plus_n_o.
        rewrite <- plus_n_Sm.
        rewrite plus_comm.
        auto.
      (*end*)
    + destruct n, n0; simpl. 
      (*added*)
      * do 2 rewrite sumrunlen_rev. rewrite sumrunlen_app_plus_distr;
        simpl; lia.
      * rewrite sumrunlen_rev. 
        assert (sumrunlen (rev ln' ++ [S n0]) = sumrunlen (rev ln') + sumrunlen [S n0]) as H.
         { rewrite sumrunlen_app_plus_distr. auto. }
        rewrite H. 
        rewrite sumrunlen_rev.
        rewrite sumrunlen_app_plus_distr. simpl.
        rewrite plus_n_o.
        assert (S (n0 + sumrunlen ln') = (sumrunlen ln' + S n0)) as H1.
         {rewrite plus_comm. rewrite plus_n_Sm. auto. }
        rewrite H1. auto.
      * rewrite sumrunlen_rev.
        rewrite sumrunlen_app_plus_distr.
        rewrite sumrunlen_rev.
        simpl.
        rewrite plus_n_o.
        rewrite sumrunlen_app_plus_distr.
        simpl. 
        rewrite <- plus_n_Sm.
        assert (n + sumrunlen ln + sumrunlen ln' = n + (sumrunlen ln + sumrunlen ln')) as Hcomm.
         {rewrite plus_assoc. auto. }
        rewrite Hcomm.        
        rewrite plus_comm. 
        auto.
      * rewrite sumrunlen_app_plus_distr.
        rewrite sumrunlen_app_plus_distr.
        rewrite sumrunlen_rev.
        rewrite sumrunlen_rev.
        simpl.
        do 2 rewrite plus_n_o.
        rewrite sumrunlen_app_plus_distr.
        simpl. 
        lia.
  - destruct a.  
    destruct col, ln, ln'; simpl; auto.
    + destruct n.
      * simpl.
        replace (0 :: ln ++ []) with ((0 :: ln) ++ [])
        by reflexivity.
        replace [0] with ([0] ++ []) by now rewrite app_nil_r.  
        repeat rewrite IHlb; simpl; lia.
      * replace (0 :: S n :: ln ++ []) with ((0 :: S n :: ln) ++ [])
        by reflexivity.
        replace [0] with ([0] ++ []) by now rewrite app_nil_r.  
        repeat rewrite IHlb; simpl; lia.
       (*end*)
    + destruct n.
      * destruct n0.
        { replace (0 :: ln ++ 0 :: ln')
        with ((0 :: ln ++ [0]) ++ ln')
        by (simpl; now rewrite <- app_assoc).
        replace (0 :: ln') with ([0] ++ ln')
         by reflexivity.
        repeat rewrite IHlb.
        replace (0 :: ln ++ [0])
         with ((0 :: ln) ++ [0])
        by reflexivity.
        repeat rewrite sumrunlen_app_plus_distr; simpl; lia. }
        { replace (0 :: ln ++ S n0 :: ln')
        with ((0 :: ln ++ [S n0]) ++ ln')
        by (simpl; now rewrite <- app_assoc).
        replace (0 :: S n0:: ln') with ([0] ++ [S n0] ++ ln')
         by reflexivity.
        repeat rewrite IHlb.
        replace (0 :: ln ++ [S n0])
         with ((0 :: ln) ++ [S n0])
        by reflexivity.
        repeat rewrite sumrunlen_app_plus_distr; simpl; lia. }
      * destruct n0.
        { replace (0 :: S n :: ln ++ 0 :: ln')
        with ((0 :: S n :: ln ++ [0]) ++ ln')
        by (simpl; now rewrite <- app_assoc).
        replace (0 :: ln') with ([0] ++ ln')
         by reflexivity.
        repeat rewrite IHlb.
        replace (0 :: S n :: ln ++ [0])
         with ((0 :: S n :: ln) ++ [0])
        by reflexivity.
        repeat rewrite sumrunlen_app_plus_distr; simpl; lia. }
        { replace (0 :: S n :: ln ++ S n0 :: ln')
        with ((0 :: S n :: ln ++ [S n0]) ++ ln')
        by (simpl; now rewrite <- app_assoc).
        replace (0 :: S n0:: ln') with ([0] ++ [S n0] ++ ln')
         by reflexivity.
        repeat rewrite IHlb.
        replace (0 :: S n :: ln ++ [S n0])
         with ((0 :: S n :: ln) ++ [S n0])
        by reflexivity.
        repeat rewrite sumrunlen_app_plus_distr; simpl; lia. }
    + replace (S n :: ln ++ []) with ((S n :: ln) ++ []) by reflexivity.
      replace [1] with ([1] ++ []) by now rewrite app_nil_r.
      repeat rewrite IHlb; simpl; lia.
    + replace (S n :: ln ++ n0 :: ln')
        with ((S n :: ln ++ [n0]) ++ ln')
        by (simpl; now rewrite <- app_assoc).
        replace (S n0:: ln') with ([S n0] ++ ln')
         by reflexivity.
        repeat rewrite IHlb.
        replace (S n :: ln ++ [n0])
         with ((S n :: ln) ++ [n0])
        by reflexivity.
        repeat rewrite sumrunlen_app_plus_distr; simpl; lia.
Qed. 

Lemma sumrunlen_l: forall lb ln,
  sumrunlen (runlenblack lb ln) =
  sumrunlen ln + sumrunlen (runlenblack lb []).
Proof. intros.
  intros; replace (runlenblack lb ln)
    with (runlenblack lb (ln ++ []))
    by (now rewrite app_nil_r); apply sumrunlen_l'.
Qed.

(****************** End of copied script ***************)

(*Lemma (page 15): The area of all objects can be obtained by summing the lengths of all 1 (black) runs*)
Lemma runlenblack_eq_area_all: forall img:image, sumrunlen (runlenblack img nil) = areasize img.
Proof.
 intro.
 induction img as [ | p pl].
 + simpl. auto.
 + destruct p. 
   destruct col.
   - simpl.
     rewrite <- IHpl.
     rewrite runlen_0_nil.
     auto.
   - simpl.
     rewrite <- IHpl.
     simpl.
     rewrite sumrunlen_l.
     simpl. 
     auto.
Qed.

(*****************************************************************)
(**************** Distance Measures (page 28) ********************)
(*****************************************************************)

Definition modminus (n m: nat) : nat :=
 if n <? m then m - n else n - m. 

Notation "{ m -- n }" := (modminus m n).

(*City block distance between any two pixels.*)
Definition citydist (p1 p2: pixel) : nat :=
  match p1, p2 with
 | B{r1,c1,_}, B{r2,c2,_} => {r1--r2} + {c1--c2}
  end.

(*Property 1a: d(p,q) >= 0*)
Lemma distcb_min: forall p q, citydist p q >= 0.
Proof. 
 intros.
 destruct p as [r1 c1 col1]. 
 destruct q as [r2 c2 col2].
 simpl.
 lia.
Qed.

(*Property 1b: d(p,q) = 0, iff p = q*) 
Lemma distcb_eq_0: forall p q, eqpixel p q = true -> citydist p q = 0.
Proof. 
 intros.
 destruct p as [r1 c1 col1].
 destruct q as [r2 c2 col2].
 simpl.
 unfold eqpixel in *.
 do 2 rewrite andb_true_iff in H.
 inversion H.
 inversion H0.
 assert (r1 = r2) as Hreq.
 apply beq_nat_true; auto.
 assert (c1 = c2) as Hceq.
 apply beq_nat_true; auto.
 rewrite Hreq.
 rewrite Hceq.
 unfold modminus.
 destruct ltb.
 destruct ltb.
 lia.
 lia.
 destruct ltb. 
 lia.
 lia.
Qed.

Lemma ltb_dec: forall x y, x <? y = true \/ x <? y = false.
Proof. 
 intros. 
 destruct ltb. 
 + left; auto. 
 + right; auto.
Qed. 

(*
Lemma ltb_minus_0: forall r1 r2 c1 c2, 
 r1 < r2 -> c1 < c2 -> r2 - r1 + (c2 - c1) = 0 -> r1 = r2 /\ c1 = c2.
Proof. 
 intros.
Admitted.

(*Temp: Equivalence???: p = q iff d(p,q) = 0*) 
(*Proof of the reverse is not possible as the citydist does not take the colour of the pixels
into consideration. So citydist p q = 0 does not mean, their colours are also equal, so
eqpixel p q = true can not be proved. *)
Lemma distcb_equiv_0: forall p q, citydist p q = 0 -> eqpixel p q = true.
Proof. 
 intros.
 destruct p as [r1 c1 col1].
 destruct q as [r2 c2 col2].
 simpl.
 do 2 rewrite andb_true_iff.
 unfold citydist in *.
 unfold modminus in *.
 assert (r1 <? r2 = true \/ r1 <? r2 = false) by now apply ltb_dec.
 assert (c1 <? c2 = true \/ c1 <? c2 = false) by now apply ltb_dec.
 destruct H0; destruct H1.
 * rewrite H0 in H; rewrite H1 in H.
Admitted.
 *)


(*Modified from Compare_dec.v*)
Definition lt_eq_lt_dec n m : n < m \/ n = m \/ m < n.
Proof.
  induction n in m |- *; destruct m; auto with arith.
  destruct (IHn m) as [H|H]; auto with arith.
  destruct H; auto with arith.
Qed.

(*Copied from GT.v*)
Lemma gt_asym n m : n > m -> ~ m > n.
Proof Nat.lt_asymm _ _.


(*Property 2: d(p,q) = d(q,p)*)
Lemma distcb_comm: forall p q, citydist p q = citydist q p.
Proof. 
 intros.
 destruct p as [r1 c1 col1].
 destruct q as [r2 c2 col2].
 simpl. 
 unfold modminus.
 assert (r1 < r2 \/ r1 = r2 \/ r2 < r1 ) as Hr12.
 apply lt_eq_lt_dec.
 assert (c1 < c2 \/ c1 = c2 \/ c2 < c1 ) as Hc12.
 apply lt_eq_lt_dec.
 destruct Hr12; destruct Hc12; simpl; auto.
 assert (~ r2 < r1) as Hneqr. apply gt_asym; auto.
 assert (~ c2 < c1) as Hneqc. apply gt_asym; auto.
 rewrite <- ltb_lt_not in Hneqr.
 rewrite <- ltb_lt_not in Hneqc.
 + rewrite <- ltb_lt in H. rewrite <- ltb_lt in H0. 
   rewrite H; rewrite H0. rewrite Hneqr. rewrite Hneqc. auto.
 + destruct H0.
   - assert (~ r2 < r1) as Hneqr. apply gt_asym; auto. 
     rewrite <- ltb_lt in H.
     rewrite <- ltb_lt_not in Hneqr.
     rewrite H. rewrite H0. rewrite Hneqr. auto.
   - assert (~ r2 < r1) as Hneqr. apply gt_asym; auto. 
     assert (~ c1 < c2) as Hneqc. apply gt_asym; auto. 
     rewrite <- ltb_lt in H.
     rewrite <- ltb_lt in H0.
     rewrite <- ltb_lt_not in Hneqr.
     rewrite <- ltb_lt_not in Hneqc.
     rewrite H. rewrite H0. rewrite Hneqr. rewrite Hneqc. auto.
 + destruct H.
   - assert (~ c2 < c1) as Hneqc. apply gt_asym; auto. 
     rewrite <- ltb_lt in H0.
     rewrite <- ltb_lt_not in Hneqc.
     rewrite H. rewrite H0. rewrite Hneqc. auto.
   - assert (~ r1 < r2) as Hneqr. apply gt_asym; auto. 
     assert (~ c2 < c1) as Hneqc. apply gt_asym; auto. 
     rewrite <- ltb_lt in H.
     rewrite <- ltb_lt in H0.
     rewrite <- ltb_lt_not in Hneqr.
     rewrite <- ltb_lt_not in Hneqc.
     rewrite H. rewrite H0. rewrite Hneqr. rewrite Hneqc. auto.
 + destruct H; destruct H0.
  - rewrite H; rewrite H0; auto.
  - assert (~ c1 < c2) as Hneqc. apply gt_asym; auto. 
    rewrite <- ltb_lt in H0.
    rewrite <- ltb_lt_not in Hneqc.
    rewrite H. rewrite H0. rewrite Hneqc. auto.
  - assert (~ r1 < r2) as Hneqr. apply gt_asym; auto. 
    rewrite <- ltb_lt in H.
    rewrite <- ltb_lt_not in Hneqr.
    rewrite H. rewrite H0. rewrite Hneqr. auto.
  - assert (~ r1 < r2) as Hneqr. apply gt_asym; auto. 
    assert (~ c1 < c2) as Hneqc. apply gt_asym; auto.
    rewrite <- ltb_lt in H.
    rewrite <- ltb_lt in H0.
    rewrite <- ltb_lt_not in Hneqr.
    rewrite <- ltb_lt_not in Hneqc.
    rewrite H. rewrite H0. rewrite Hneqc. rewrite Hneqr. auto.
Qed. 

Lemma ltb_iff_conv m n : (n <? m) = false <-> m <= n.
Proof.
 intros.  split.
 induction m. lia. intros.
 apply Nat.leb_gt  in H . lia.
 intros. induction m. auto with arith.
 apply Nat.leb_gt . lia.
Qed.

(*Property 3: d(p,r) <= d(q,p) + d(q,r) *)
Lemma citydist_trans: forall p q r, 
citydist p r <= citydist p q + citydist q r. 
Proof. 
 intros. 
 destruct p as [r1 c1 col1].
 destruct q as [r2 c2 col2].
 destruct r as [r3 c3 col3].
 simpl. 
 unfold modminus.
 assert (r1 <? r3 = true \/ r1 <? r3 = false) as Hr13. apply ltb_dec. 
 assert (r1 <? r2 = true \/ r1 <? r2 = false) as Hr12. apply ltb_dec. 
 assert (r2 <? r3 = true \/ r2 <? r3 = false) as Hr23. apply ltb_dec. 
 assert (c1 <? c3 = true \/ c1 <? c3 = false) as Hc13. apply ltb_dec. 
 assert (c1 <? c2 = true \/ c1 <? c2 = false) as Hc12. apply ltb_dec. 
 assert (c2 <? c3 = true \/ c2 <? c3 = false) as Hc23. apply ltb_dec. 

 destruct Hr13; destruct Hr12; destruct Hr23; 
 destruct Hc13; destruct Hc12; destruct Hc23;  
 rewrite H; rewrite H0; rewrite H1; rewrite H2; rewrite H3; rewrite H4; simpl;  
 (try rewrite ltb_lt in *; 
  try rewrite ltb_iff_conv in H; 
  try rewrite ltb_iff_conv in H0;
  try rewrite ltb_iff_conv in H1;
  try rewrite ltb_iff_conv in H2;
  try rewrite ltb_iff_conv in H3;
  try rewrite ltb_iff_conv in H4); try lia.
Qed.

 
      
