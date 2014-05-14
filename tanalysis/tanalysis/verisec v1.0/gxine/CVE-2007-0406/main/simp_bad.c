#include "../constants.h"

int main ()
{
    struct sockaddr_un serv_adr;
    char               filename [FILENAME_SZ];

    /* Added for STAC: the input data must be considered tainted! */
    filename[0] = taint();
    
    /* server filename */
    filename[FILENAME_SZ-1] = EOS;
    
    /* initialize the server address structure */
    /* BAD */
    r_strcpy (serv_adr.sun_path, filename);

    return 0;
}
