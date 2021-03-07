
/* Updated 2021, March 07 */
/*******************************************************************************************************************************/
/* The subject here is establish an algorirthm to determine a SIGNED fundamental domain for non-complex number fields. */
/* This is based in the works of Diaz y Diaz, Espinoza and Friedman:                                                   */
/* Diaz y Diaz and Friedman, "Signed fundamental domain for totally real number fields" (2014) [MR4105945]             */
/* Espinoza and Friedman, "Twisters and Signed fundamental domains of number fields" (2020) [MR3198753]                */


\p 600 \\ realprecision, this real precision is necessary to compare the signs (+1 or -1) of each cone obtained below. 
/*******************************************************************************************************************************/
/*****************************************************************************/
/*                                                                           */
/*                Computing signed fundamental domains for                   */
/*               Totally real number fields, i.e. (r1,r2)=(n,0)              */
/*                                                                           */
/*****************************************************************************/
/*********************************************************************************************************************/
/*** INPUT: bnf=bnfinit(polynomial) data of a number field K=Q(theta) given; U=their totally positive units */

/*** OUTPUT: List of [N,P] of the negative and positive K-rational cones whose signs are sign(N)=-1 and sign(P)=+1 */
/*** In many cases #N + #P=(n-1)!, where n=[K:Q] the degree of K over Q */

\\lcs(G,d)=  
signedfd1(U,bnf)=
{my(b,d,S,p,n,N,P,C,w,t1,e);
t1=getwalltime();
d=bnf;
b=sign(matdet(Mat(rpl(U,d)~)));
p=d.pol;
n=d.r1+2*d.r2;  \\ degree of polynomial p
S=lper(n-1);    \\ list of all the permutations in S_{n-1}.
N=[];
P=[];
for(l=1,#S,
   e=sgnc([S[l],U],d,b);
   if(e==1,
      C=[1];
      for(j=2,n,w=vector(j-1,i,U[S[l][i]]);C=concat(C,[prd(w,p)]));
      P=concat(P,[C]);
      );
   if(e==-1,
      C=[1];
      for(j=2,n,w=vector(j-1,i,U[S[l][i]]);C=concat(C,[prd(w,p)]));
      N=concat(N,[C]);
      );
);
print1([[#N,#P],getwalltime()-t1]); 
return([N,P]);
}


/*********************************************************************************************************************/
/*****************************************************************************/
/*                                                                           */
/*                Computing signed fundamental domains for                   */
/*                 all non-totally complex number fields                     */
/*                                                                           */
/*****************************************************************************/
/*********************************************************************************************************************/
/*** INPUT: bnf=bnfinit(polynomial) data of a number field K=Q(theta) given; U=totally positive units*/

/*** OUTPUT: List of [N,P] of the negative and positive K-rational cones whose signs are sign(N)=-1 and sign(P)=+1 */
/*** In many cases #N + #P=(n-1)!*3^{r2}, where n=[K:Q] the degree of K over Q and r2=#of pairs of complex places*/

\\listCsG(U,bnf)=
signedfd2(U,bnf)=
{my(SC,N,P,h,S,sg,C,L,t1,a);
t1=getwalltime();
SC=ComplexG(U,bnf); \\ the simplicial complex in Z^{n-1} with (n-1)!*3^{r2} simpliciales of dimension (n-1).
L=twisterG(bnf);    \\#L=3^r2 elements in k+, called twisters
a=signR(U,bnf);
N=[];
P=[];
h=length(SC);
for(j=1,h,
   S=SC[j];
   [sg,C]=signC(S,L,U,bnf,a);
   if(sg==1,P=concat(P,[C]));
   if(sg==-1,N=concat(N,[C])); \\ Cones with sign equal to zero is not consider in our "signed fundamental domain".
  );
print1([[#N,#P],getwalltime()-t1]); 
return([N,P]); 
}








