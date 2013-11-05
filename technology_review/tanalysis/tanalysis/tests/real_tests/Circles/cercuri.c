#include <stdio.h>
#include <math.h>
#define PI 3.14
int n,x,X,y,Y,r1,r2;

FILE* in;
FILE* out;


/* prototipurile functiilor */
double distanta(int x1,int x2,int y1,int y2);
double arie(int x1,int x2,int y1,int y2,int r1,int r2);
double arie_cerc_mic(int x1,int x2,int y1,int y2,int r1,int r2);
int sunt_bune(int x1,int y1,int r1,int x2,int y2,int r2);





void main()
{	
	int i;
	in = fopen("date.in","r");
	out = fopen("rez.out","w");
	/* citim numarul de teste efectuate */
	fscanf(in, "%d",&n);

	/* citim cele n seturi de cercuri si verificam relatiile dintre ele */
	for(i=1;i<=n;i++)
		{fscanf(in,"%d%d%d%d%d%d",&x,&y,&r1,&X,&Y,&r2);
			if(sunt_bune(x,y,r1,X,Y,r2))   /* verificam conditiile de existenta */
			{					           /*verificam relatiile dintre cercuri: */
				if(distanta(x,X,y,Y)>(r1+r2)) fprintf(out,"EX 0.00\n");
						else if(distanta(x,X,y,Y)==(r1+r2)) fprintf(out,"TE 0.00\n");
								else if(distanta(x,X,y,Y)==(r1-r2)) fprintf(out,"TI %.2lf\n",arie_cerc_mic(x,X,y,Y,r1,r2));
									else if((distanta(x,X,y,Y)<(r1+r2))&&(distanta(x,X,y,Y)>abs(r1-r2))) fprintf(out,"SE %.2lf\n",arie(x,X,y,Y,r1,r2));
										else fprintf(out,"IN %.2lf\n",arie_cerc_mic(x,X,y,Y,r1,r2));
			}
			 
			else fprintf(out,"ERROR\n");
			
		}
}


/* calculam aria intersectiei a doua cercuri */
double arie(int x1,int x2,int y1,int y2,int r1,int r2)
{
	double S=0, d=distanta(x1,x2,y1,y2),
			u1=2*acos((pow(r1,2)-pow(r2,2)+pow(d,2))/(2*d*r1)),
			u2=2*acos((pow(d,2)-pow(r1,2)+pow(r2,2))/(2*r2*d)),
		    S1=pow(r1,2)*sin(u1)/2,
			S2=u1*pow(r1,2)/2,
			S3=pow(r2,2)*sin(u2)/2,
			S4=u2*pow(r2,2)/2;

    S=S2-S1+S4-S3;
return S;									
}

/* verificam daca sunt corecte datele de intrare */
int sunt_bune(int x1,int y1,int r1,int x2,int y2,int r2)
{
	if(x1<0||x2<0||y1<0||y2<0||x1>1000||x2>1000||y1>1000||y2>1000||r1<1||r2<1||r1>1000||r2>1000)return 0;
		else return 1;
}

/* calculam aria cercului mic, inclus in cercul mare */
double arie_cerc_mic(int x1,int x2,int y1,int y2,int r1,int r2)
{
	if(r2<r1)
			return PI*pow(r2,2);
	else return PI*pow(r1,2);
}

/* calculam distanta dintre centrele cercurilor */
double distanta(int x1,int x2,int y1,int y2)
{
	return sqrt(pow(x2-x1,2)+pow(y2-y1,2));
}




