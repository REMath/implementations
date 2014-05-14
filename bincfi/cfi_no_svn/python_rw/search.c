struct tuple{
	long old;
	long new;

};
struct tuple array[1024] = { {0,2},{1025,3},{1026,5},{1027,7}};
#include <stdio.h>
long insn_begin;
long insn_end;
long old_addr;
long insn_mask;
long mapping_size;
int idx;
int i;
void main(){
	i=0;
	int oirg_addr;
	mapping_size = 1024;
	insn_begin=0;
	insn_end=2000;
	insn_mask=1<<10 - 1;
	old_addr=1026;
	oirg_addr = old_addr;
	search();
	printf("search addr %d, new addr:%d\n",oirg_addr, old_addr);
	old_addr=0;
	oirg_addr = old_addr;
	search();
	printf("search addr %d, new addr:%d\n",oirg_addr, old_addr);
	old_addr=1027;
	oirg_addr = old_addr;
	search();
	printf("search addr %d, new addr:%d\n",oirg_addr, old_addr);
	old_addr=2027;
	oirg_addr = old_addr;
	search();
	printf("search addr %d, new addr:%d\n",oirg_addr, old_addr);


}
void search(){
	if(old_addr <insn_begin || old_addr >insn_end)
		goto err;
	//mask to get the index
	idx=(old_addr - insn_begin) & insn_mask;
	for (i = 0;i<mapping_size;i++,idx = (idx+1) & insn_mask){
		if(array[idx].old != old_addr)
			continue;
		else{
			//empty here
			old_addr = array[idx].new;
			return;
		}
	} 
err:
	return;
}
