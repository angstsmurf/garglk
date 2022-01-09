/*
 *	ScottFree Revision 1.14
 *
 *
 *	This program is free software; you can redistribute it and/or
 *	modify it under the terms of the GNU General Public License
 *	as published by the Free Software Foundation; either version
 *	2 of the License, or (at your option) any later version.
 *
 *
 *	You must have an ANSI C compiler to build this program.
 */

/*
 * Parts of this source file (mainly the Glk parts) are copyright 2011
 * Chris Spiegel.
 *
 * Some notes about the Glk version:
 *
 * o Room descriptions, exits, and visible items can, as in the
 *   original, be placed in a window at the top of the screen, or can be
 *   inline with user input in the main window.  The former is default,
 *   and the latter can be selected with the -w flag.
 *
 * o Game saving and loading uses Glk, which means that providing a
 *   save game file on the command-line will no longer work.  Instead,
 *   the verb "restore" has been special-cased to call GameLoad(), which
 *   now prompts for a filename via Glk.
 *
 * o The local character set is expected to be compatible with ASCII, at
 *   least in the printable character range.  Newlines are specially
 *   handled, however, and converted to Glk's expected newline
 *   character.
 */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <ctype.h>
#include <stdarg.h>
#include <time.h>

#include "glk.h"
#include "glkstart.h"

#include "bsd.h"
#include "scott.h"

#ifdef __GNUC__
__attribute__((__format__(__printf__, 2, 3)))
#endif
static void Display(winid_t w, const char *fmt, ...)
{
	va_list ap;
	char msg[2048];

	va_start(ap, fmt);
	vsnprintf(msg, sizeof msg, fmt, ap);
	va_end(ap);

	/* Map newline to a Glk-compatible newline. */
	for(size_t i = 0; msg[i] != 0; i++)
	{
		if(msg[i] == '\n') msg[i] = 10;
	}

	glk_put_string_stream(glk_window_get_stream(w), msg);
}

static void Delay(int seconds)
{
	event_t ev;

	if(!glk_gestalt(gestalt_Timer, 0))
		return;

	glk_request_timer_events(1000 * seconds);

	do
	{
		glk_select(&ev);
	} while(ev.type != evtype_Timer);

	glk_request_timer_events(0);
}

static Header GameHeader;
static Item *Items;
static Room *Rooms;
static const char **Verbs;
static const char **Nouns;
static const char **Messages;
static Action *Actions;
static int LightRefill;
static char NounText[16];
static int Counters[16];	/* Range unknown */
static int CurrentCounter;
static int SavedRoom;
static int RoomSaved[16];	/* Range unknown */
static int Options;		/* Option flags set */
static int Width;		/* Terminal width */
static int TopHeight;		/* Height of top window */

static int file_baseline_offset = 0;

static int split_screen = 1;
static winid_t Bottom, Top;

#define TRS80_LINE	"\n<------------------------------------------------------------>\n"

#define MyLoc	(GameHeader.PlayerRoom)

static long BitFlags=0;	/* Might be >32 flags - I haven't seen >32 yet */

static void Fatal(const char *x)
{
	Display(Bottom, "%s\n", x);
	glk_exit();
}

static void ClearScreen(void)
{
	glk_window_clear(Bottom);
}

static void *MemAlloc(int size)
{
	void *t=(void *)malloc(size);
	if(t==NULL)
		Fatal("Out of memory");
	return(t);
}

static int RandomPercent(int n)
{
	unsigned int rv=rand()<<6;
	rv%=100;
	if(rv<n)
		return(1);
	return(0);
}

static int CountCarried(void)
{
	int ct=0;
	int n=0;
	while(ct<=GameHeader.NumItems)
	{
		if(Items[ct].Location==CARRIED)
			n++;
		ct++;
	}
	return(n);
}

static const char *MapSynonym(const char *word)
{
	int n=1;
	const char *tp;
	static char lastword[16];	/* Last non synonym */
	while(n<=GameHeader.NumWords)
	{
		tp=Nouns[n];
		if(*tp=='*')
			tp++;
		else
			strcpy(lastword,tp);
		if(xstrncasecmp(word,tp,GameHeader.WordLength)==0)
			return(lastword);
		n++;
	}
	return(NULL);
}

static int MatchUpItem(const char *text, int loc)
{
	const char *word=MapSynonym(text);
	int ct=0;

	if(word==NULL)
		word=text;

	while(ct<=GameHeader.NumItems)
	{
		if(Items[ct].AutoGet && Items[ct].Location==loc &&
			xstrncasecmp(Items[ct].AutoGet,word,GameHeader.WordLength)==0)
			return(ct);
		ct++;
	}
	return(-1);
}

static char *ReadString(FILE *f)
{
	char tmp[1024];
	char *t;
	int c,nc;
	int ct=0;
	do
	{
		c=fgetc(f);
	}
	while(c!=EOF && isspace(c));
	if(c!='"')
	{
		Fatal("Initial quote expected");
	}
	do
	{
		c=fgetc(f);
		if(c==EOF)
			Fatal("EOF in string");
		if(c=='"')
		{
			nc=fgetc(f);
			if(nc!='"')
			{
				ungetc(nc,f);
				break;
			}
		}
		if(c=='`')
			c='"'; /* pdd */

		/* Ensure a valid Glk newline is sent. */
		if(c=='\n')
			tmp[ct++]=10;
		/* Special case: assume CR is part of CRLF in a
		 * DOS-formatted file, and ignore it.
		 */
		else if(c==13)
			;
		/* Pass only ASCII to Glk; the other reasonable option
		 * would be to pass Latin-1, but it's probably safe to
		 * assume that Scott Adams games are ASCII only.
		 */
		else if((c >= 32 && c <= 126))
			tmp[ct++]=c;
		else
			tmp[ct++]='?';
	}
	while(1);
	tmp[ct]=0;
	t=MemAlloc(ct+1);
	memcpy(t,tmp,ct+1);
	return(t);
}

size_t get_file_length(FILE *in) {
    if (fseek(in, 0, SEEK_END) == -1)
    {
        return 0;
    }
    size_t file_length = ftell(in);
    if (file_length == -1)
    {
        return 0;
    }
    return file_length;
}

int rotate_left_with_carry(uint8_t *byte, int last_carry)
{
    int carry = ((*byte & 0x80) > 0);
    *byte = *byte << 1;
    if (last_carry)
        *byte = *byte | 0x01;
    return carry;
}

int rotate_right_with_carry(uint8_t *byte, int last_carry)
{
    int carry = ((*byte & 0x01) > 0);
    *byte = *byte >> 1;
    if (last_carry)
        *byte = *byte | 0x80;
    return carry;
}

int decompress_one(uint8_t *bytes) {
    uint8_t result = 0;
    int carry;
    for (int i = 0; i < 5; i++)
    {
        carry = 0;
        for (int j = 0; j < 5; j++)
        {
            carry = rotate_left_with_carry(bytes+4-j, carry);
        }
        rotate_left_with_carry(&result, carry);
    }
    return result;
}


static char *decompressed(uint8_t *source, int stringindex)
{
    // Lookup table
    const char *alphabet = " abcdefghijklmnopqrstuvwxyz'\x01,.\x00";

    int pos, c, uppercase, i, j;
    uint8_t decompressed[256];
    uint8_t buffer[5];
    int idx = 0;

    // Find the start of the compressed message
    for(int i = 0; i < stringindex; i++) {
        pos = *source;
        pos = pos & 0x7F;
        source += pos;
    };

    uppercase = ((*source & 0x40) == 0); // Test bit 6

    source++;
    do {
        // Get five compressed bytes
        for (i = 0; i < 5; i++) {
            buffer[i] = *source++;
        }
        for (j = 0; j < 8; j++) {
            // Decompress one character:
            int next = decompress_one(buffer);

            c = alphabet[next];

            if (c == 0x01) {
                uppercase = 1;
                c = ' ';
            }

            if (c >= 'a' && uppercase) {
                c = toupper(c);
                uppercase = 0;
            }
            decompressed[idx++] = c;

            if (idx > 255)
                return NULL;

            if (idx == 255)
                c = 0; // We've gone too far, return

            if (c == 0) {
                char *result = malloc(idx);
                memcpy(result, decompressed, idx);
                return result;
            } else if (c == '.' || c == ',') {
                if (c == '.')
                    uppercase = 1;
                decompressed[idx++] = ' ';
            }
        }
    } while (idx < 0xff);
    return NULL;
}

static char *decompress_text(FILE *p, int offset, int index)
{
    size_t length = get_file_length(p);
    uint8_t *buf = (uint8_t *)malloc(length);
    fseek(p, 0, SEEK_SET);
    fread(buf, sizeof *buf, length, p);

    //    offset = 0x912c; // Messages
    //    offset = 0x9B53; // Room descriptions
    //    offset = 0x9B66; // Item descriptions

    uint8_t *mem = (uint8_t *)malloc(0xFFFF);
    memset(mem, 0, 0xffff);
    for (int i = 0; i<length; i++) {
        mem[i+16357] = buf[i];
    }

    char *text = decompressed(mem+offset, index);
    free(mem);
    return text;
}

int header[36];

void read_header(FILE *in) {
    int i,value;
    for (i = 0; i < 36; i++)
    {
        value = fgetc(in) + 256 * fgetc(in);
        header[i] = value;
    }
}

void read_dictionary(FILE *ptr)
{
    char dictword[6];
    int offset = 0x591B;
tryagain:



    fseek(ptr, offset ,SEEK_SET);

    char c = 0;
    int wordnum = 0;
    int charindex = 0;

    do {
        for (int i = 0; i < 4; i++)
        {
            c=fgetc(ptr);
            if (charindex == 0) {
                if (c >= 'a')
                {
                    c = toupper(c);
                } else {
                    dictword[charindex++] = '*';
                }
            }


            dictword[charindex++] = c;

        }
        dictword[charindex] = 0;


        if (wordnum < 69)
        {
            Verbs[wordnum] = malloc(charindex+1);
            memcpy((char *)Verbs[wordnum], dictword, charindex+1);
            //            if (wordnum == 0 && strncmp(Verbs[wordnum], "AUTO", 4) != 0) {
            //                offset++;
            //                goto tryagain;
            //            }
            //            fprintf(stderr, "Verb %d: \"%s\"\n", wordnum, Verbs[wordnum]);
        } else {
            Nouns[wordnum-69] = malloc(charindex+1);
            memcpy((char *)Nouns[wordnum-69], dictword, charindex+1);
            //            fprintf(stderr, "Noun %d: \"%s\"\n", wordnum-69, Nouns[wordnum-69]);
        }
        wordnum++;
        //      }
        //        if (c != 0 && !isascii(c))
        //            return;
        charindex = 0;
    } while (wordnum <= 203);

    for (int i = 0; i < 66; i++) {
        Verbs[69 + i] = "\0";
        //        fprintf(stderr, "Verb %d: \"%s\"\n", 69 + i, Verbs[69 + i]);
    }
    //    fprintf(stderr, "Found valid dictionary at offset %d\n", offset);

}

int sanity_check_header(void) {

    int16_t v = header[1]; // items
    if (v < 10 || v > 500)
        return 0;
    v = header[2]; // actions
    if (v < 100 || v > 500)
        return 0;
    v = header[3]; // word pairs
    if (v < 50 || v > 200)
        return 0;
    v = header[4]; // Number of rooms
    if (v < 10 || v > 100)
        return 0;
    v = header[5]; // Number of Messages
    if (v < 10 || v > 255)
        return 0;

    return 1;
}

static void LoadDatabase(FILE *f, int loud)
{
    int ni,na,nw,nr,mc,pr,tr,wl,lt,mn,trm;
    int ct;
    //    short lo;
    Action *ap;
    Room *rp;
    Item *ip;

    /* Load the header */

    size_t file_length = get_file_length(f);

    size_t pos = 0x3b5a;
    fseek(f, pos, SEEK_SET);
    read_header(f);
    if (sanity_check_header() == 0) {
        pos = 0;

        while (sanity_check_header() == 0) {
            pos++;
            fseek(f, pos, SEEK_SET);
            read_header(f);
            if (pos >= file_length - 24) {
                fprintf(stderr, "found no valid header in file\n");
                exit(1);
            }
        }
    }

    file_baseline_offset = pos - 0x494d;

    ni = header[1];
    na = header[2];
    nw = header[3];
    nr = header[4];
    mc = header[5];
    wl = header[6];
    mn = header[7];
    pr = 1;
    //    pr = 46;
    //    pr = 86;
    tr = 0;
    lt = -1;
    trm = 0;

    GameHeader.NumItems=ni;
    Items=(Item *)MemAlloc(sizeof(Item)*(ni+1));
    GameHeader.NumActions=na;
    Actions=(Action *)MemAlloc(sizeof(Action)*(na+1));
    GameHeader.NumWords=nw;
    GameHeader.WordLength=wl;
    Verbs=MemAlloc(sizeof(char *)*(nw+1));
    Nouns=MemAlloc(sizeof(char *)*(nw+1));
    GameHeader.NumRooms=nr;
    Rooms=(Room *)MemAlloc(sizeof(Room)*(nr+1));
    GameHeader.MaxCarry=mc;
    GameHeader.PlayerRoom=pr;
    GameHeader.Treasures=tr;
    GameHeader.LightTime=lt;
    LightRefill=lt;
    GameHeader.NumMessages=mn;
    Messages=MemAlloc(sizeof(char *)*(mn+1));
    GameHeader.TreasureRoom=trm;

    int offset;


#pragma mark Item flags
    offset = 0x4961 + file_baseline_offset;

    //    fprintf(stderr, "File offset before reading item flags: %ld\n", ftell(f));

jumpItemFlags:
    fseek(f,offset,SEEK_SET);

    /* Load the item flags */

    ip=Items;

    for (ct = 0; ct <= GameHeader.NumItems; ct++) {
        ip->Flag = fgetc(f);
        if((ct == 17 && (ip->Flag & 127) != 1)) {
            offset++;
            goto jumpItemFlags;
        }
        ip++;
    }


    //    fprintf(stderr, "Found item flags at %d\n", offset);
    //    fprintf(stderr, "Difference from expected 0x4961: %d\n", offset - 0x4961);
    //    fprintf(stderr, "Difference from expected 0x4961 + file_baseline_offset(%d) : %d\n", file_baseline_offset, offset - (0x4961 + file_baseline_offset));
    //    fprintf(stderr, "File offset after reading item flags: %ld\n", ftell(f));



    offset = 0x46CC + file_baseline_offset;

jumpItemImages:
    fseek(f,offset,SEEK_SET);

#pragma mark item images

    /* Load the item images */

    ip=Items;

    for (ct = 0; ct <= GameHeader.NumItems; ct++) {
        ip->Image = fgetc(f);
        if ((ct == 17 && ip->Image != 138) || (ip->Image > 138 && ip->Image != 255)) {
            offset++;
            goto jumpItemImages;
        }
        ip++;
    }
    //    fprintf(stderr, "Found item images at %x\n", offset);
    //    fprintf(stderr, "File offset after reading item images: %lx\n", ftell(f));
    //

    offset = 0x4A5D  + file_baseline_offset;;
jumpHere:

#pragma mark actions

    /* Load the actions */

    fseek(f,offset,SEEK_SET);
    ct=0;

    Actions=(Action *)malloc(sizeof(Action)*(na+1));
    ap=Actions;

    int value, cond, comm;
    while(ct<na+1)
    {
        value = fgetc(f) + 256 * fgetc(f); /* verb/noun */
        ap->Vocab = value;

        int verb = value;

        int noun=verb%150;
        verb/=150;

        if (noun < 0 || noun > nw || verb < 0 || verb > nw) {
            offset--;
            goto jumpHere;
        }

        value = fgetc(f); /* count of actions/conditions */
        cond = value & 0x1f;
        comm = (value & 0xe0) >> 5;

        //        fprintf(stderr, "Action %d conditions: %d commands %d\n", ct, cond, comm);

        for (int j = 0; j < 5; j++)
        {
            if (j < cond) value = fgetc(f) + 256 * fgetc(f); else value = 0;
            ap->Condition[j] = value;
        }
        for (int j = 0; j < 2; j++)
        {
            if (j < comm) value = fgetc(f) + 256 * fgetc(f); else value = 0;
            ap->Action[j] = value;
        }

        ap++;
        ct++;
    }
    //
    //    fprintf(stderr, "Found valid actions at offset %d\n", offset);
    //    fprintf(stderr, "File offset after reading actions: %ld\n", ftell(f));


    //    for (int i = 0; i <= GameHeader.NumActions; i++) {
    //        for (int j = 0; j < 2; j++) {
    //
    //            int value = Actions[i].Action[j];
    //            int action1 = value % 150;
    //            //fprintf(stderr, "Action %d noun: %s\n", ct, Nouns[noun]);
    //            int action2 = value / 150;
    //
    //            if (action1 == 10 || action2 == 10) {
    //                print_action_info(i);
    //                break;
    //            }
    //        }
    //    }





#pragma mark dictionary

    fseek(f, 0x591B + file_baseline_offset,SEEK_SET);

    read_dictionary(f);

    //    for (int i = 0; i <= na; i++)
    //    {
    //        int vocab = Actions[i].Vocab;
    //
    //        int verb = vocab;
    //
    //        int noun=verb%150;
    //
    //        verb/=150;
    //
    //        fprintf(stderr, "Action %d verb: %s (%d) noun: %s (%d)\n", i,  Verbs[verb], verb, Nouns[noun], noun);
    //    }

    //    fprintf(stderr, "File offset after reading dictionary: %ld\n", ftell(f));

    offset = 23627 + file_baseline_offset;

#pragma mark room connections
try_again_connections:

    fseek(f,offset,SEEK_SET);

    ct=0;
    rp=Rooms;
    //    if(loud)

    while(ct<nr)
    {
        for (int j= 0; j < 6; j++) {
            rp->Exits[j] = fgetc(f);
            if (rp->Exits[j] < 0 || rp->Exits[j] > nr || (ct == 11 && j == 4 && rp->Exits[j] != 1) || (ct == 1 && j == 5 && rp->Exits[j] != 11)) {
                offset++;
                goto try_again_connections;
            }

        }
        ct++;
        rp++;
    }
    //
    //    fprintf(stderr, "Reading %d X 6 room connections, total of %d bytes.\n",nr, nr * 6);
    //    fprintf(stderr, "Found room connections at offset %d.\n", offset);
    //
    //    fprintf(stderr, "File offset after reading room connections: %ld\n", ftell(f));

#pragma mark item locations

    offset = 0x5e3d + file_baseline_offset;
jumpItemLoc:

    fseek(f,offset,SEEK_SET);

    ct=0;
    ip=Items;
    while(ct<ni+1)
    {
        ip->Location=fgetc(f);
        if ((ct == 41 && ip->Location != 11) || (ct == 123 && ip->Location != 11)) {
            offset++;
            goto jumpItemLoc;
        }

        ip->InitialLoc=ip->Location;
        ip++;
        ct++;
    }

    //    fprintf(stderr, "Found item locations at offset: %d\n", offset);
    //    fprintf(stderr, "Difference from expected 0x5e3d: %d\n", offset - 0x5e3d);
    //    fprintf(stderr, "Difference from expected 0x5e3d + file_baseline_offset(%d) : %d\n", file_baseline_offset, offset - (0x5e3d + file_baseline_offset));
    //
    //    fprintf(stderr, "File offset after reading item locations : %ld\n", ftell(f));

#pragma mark messages

    offset = 0x9ea0 + file_baseline_offset;
    if(loud)
        fprintf(stderr, "Reading %d messages.\n",mn);

jumpHereMessages:

    ct=0;

    while(ct<mn+1)
    {
        Messages[ct] = decompress_text(f, offset, ct);


        //        if (Messages[ct] == NULL || (ct == 0 && (Messages[ct] == NULL || strncmp(Messages[ct], ". ", 2) != 0))) {
        //            offset--;
        //            if (offset > 0xFFFF)
        //                fprintf(stderr, "Error");
        //            goto jumpHereMessages;
        //        }
        //        fprintf(stderr, "Message %d : \"%s\"\n", ct, Messages[ct]);
        ct++;
    }

    //    fprintf(stderr, "Found valid messages at %d\n", offset);

#pragma mark rooms

    offset = 42928 + file_baseline_offset;


    if(loud)
        fprintf(stderr, "Reading %d rooms.\n",nr);

jumpHereRooms:

    ct=0;
    rp=Rooms;

    //    char c=0;

    //    rp->Text = malloc(3);
    //    strcpy(rp->Text, ". \0");
    //    //    fprintf(stderr, "Room 0 : \"%s\"\n", rp->Text);
    //    rp++;

    //    int actual_room_number = 0;

    do {
        rp->Text = decompress_text(f, offset, ct);

        //        if ((ct == 1 && (rp->Text == NULL || strncmp(rp->Text, "On the Banshee", 14) != 0))) {
        //            offset++;
        //            goto jumpHereRooms;
        //        }


        //        fprintf(stderr, "Room %d : \"%s\"\n", ct, Rooms[ct].Text);
        *(rp->Text) = tolower(*(rp->Text));
        ct++;
        rp++;
    } while (ct<GameHeader.NumRooms);

    //    fprintf(stderr, "Found room descriptions at offset %d.\n", offset);


#pragma mark items

    //    offset = 0x3e67 + file_baseline_offset;
    offset = 44229 + file_baseline_offset;
    if(loud)
        fprintf(stderr, "Reading %d items.\n",ni);


    ct=0;

    ip=Items;

    do {
        ip->Text = decompress_text(f, offset, ct);
        //
        //                if ((ct == 0 && (ip->Text == NULL || strncmp(ip->Text, "Lagash", 6) != 0))) {
        //                    offset++;
        //                    goto try_again;
        //                }
        //        fprintf(stderr, "Item %d : \"%s\"\n", ct,  ip->Text);

        ip->AutoGet=strchr(ip->Text,'.');
        //            /* Some games use // to mean no auto get/drop word! */
        if(ip->AutoGet)
        {
            char *t;
            *ip->AutoGet++=0;
            ip->AutoGet++;
            t=strchr(ip->AutoGet,'.');
            if(t!=NULL)
                *t=0;
            for (int i = 1; i < 4; i++)
                *(ip->AutoGet+i) = toupper(*(ip->AutoGet+i));
            //            fprintf(stderr, "Autoget: \"%s\"\n", ip->AutoGet);
        }


        ct++;
        ip++;
    } while(ct<ni+1);

    if(loud)
        fprintf(stderr, "%d.\nLoad Complete.\n\n",ct);
}

static void Output(const char *a)
{
	Display(Bottom, "%s", a);
}

static void OutputNumber(int a)
{
	Display(Bottom, "%d", a);
}

static void Look(void)
{
	static char *ExitNames[6]=
	{
		"North","South","East","West","Up","Down"
	};
	Room *r;
	int ct,f;
	int pos;

	if(split_screen)
		glk_window_clear(Top);

	if((BitFlags&(1<<DARKBIT)) && Items[LIGHT_SOURCE].Location!= CARRIED
	            && Items[LIGHT_SOURCE].Location!= MyLoc)
	{
		if(Options&YOUARE)
			Display(Top,"You can't see. It is too dark!\n");
		else
			Display(Top,"I can't see. It is too dark!\n");
		if (Options & TRS80_STYLE)
			Display(Top,TRS80_LINE);
		return;
	}
	r=&Rooms[MyLoc];
	if(*r->Text=='*')
		Display(Top,"%s\n",r->Text+1);
	else
	{
		if(Options&YOUARE)
			Display(Top,"You are in a %s\n",r->Text);
		else
			Display(Top,"I'm in a %s\n",r->Text);
	}
	ct=0;
	f=0;
	Display(Top,"\nObvious exits: ");
	while(ct<6)
	{
		if(r->Exits[ct]!=0)
		{
			if(f==0)
				f=1;
			else
				Display(Top,", ");
			Display(Top,"%s",ExitNames[ct]);
		}
		ct++;
	}
	if(f==0)
		Display(Top,"none");
	Display(Top,".\n");
	ct=0;
	f=0;
	pos=0;
	while(ct<=GameHeader.NumItems)
	{
		if(Items[ct].Location==MyLoc)
		{
			if(f==0)
			{
				if(Options&YOUARE)
				{
					Display(Top,"\nYou can also see: ");
					pos=18;
				}
				else
				{
					Display(Top,"\nI can also see: ");
					pos=16;
				}
				f++;
			}
			else if (!(Options & TRS80_STYLE))
			{
				Display(Top," - ");
				pos+=3;
			}
			if(pos+strlen(Items[ct].Text)>(Width-10))
			{
				pos=0;
				Display(Top,"\n");
			}
			Display(Top,"%s",Items[ct].Text);
			pos += strlen(Items[ct].Text);
			if (Options & TRS80_STYLE)
			{
				Display(Top,". ");
				pos+=2;
			}
		}
		ct++;
	}
	Display(Top,"\n");
	if (Options & TRS80_STYLE)
		Display(Top,TRS80_LINE);
}

static int WhichWord(const char *word, const char **list)
{
	int n=1;
	int ne=1;
	const char *tp;
	while(ne<=GameHeader.NumWords)
	{
		tp=list[ne];
		if(*tp=='*')
			tp++;
		else
			n=ne;
		if(xstrncasecmp(word,tp,GameHeader.WordLength)==0)
			return(n);
		ne++;
	}
	return(-1);
}

static void LineInput(char *buf, size_t n)
{
	event_t ev;

	glk_request_line_event(Bottom, buf, n - 1, 0);

	while(1)
	{
		glk_select(&ev);

		if(ev.type == evtype_LineInput)
			break;
		else if(ev.type == evtype_Arrange && split_screen)
			Look();
	}

	buf[ev.val1] = 0;
}

static void SaveGame(void)
{
	strid_t file;
	frefid_t ref;
	int ct;
	char buf[128];

	ref = glk_fileref_create_by_prompt(fileusage_TextMode | fileusage_SavedGame, filemode_Write, 0);
	if(ref == NULL) return;

	file = glk_stream_open_file(ref, filemode_Write, 0);
	glk_fileref_destroy(ref);
	if(file == NULL) return;

	for(ct=0;ct<16;ct++)
	{
		snprintf(buf, sizeof buf, "%d %d\n",Counters[ct],RoomSaved[ct]);
		glk_put_string_stream(file, buf);
	}
	snprintf(buf, sizeof buf, "%ld %d %hd %d %d %hd\n",BitFlags, (BitFlags&(1<<DARKBIT))?1:0,
		MyLoc,CurrentCounter,SavedRoom,GameHeader.LightTime);
	glk_put_string_stream(file, buf);
	for(ct=0;ct<=GameHeader.NumItems;ct++)
	{
		snprintf(buf, sizeof buf, "%hd\n",(short)Items[ct].Location);
		glk_put_string_stream(file, buf);
	}

	glk_stream_close(file, NULL);
	Output("Saved.\n");
}

static void LoadGame(void)
{
	strid_t file;
	frefid_t ref;
	char buf[128];
	int ct=0;
	short lo;
	short DarkFlag;

	ref = glk_fileref_create_by_prompt(fileusage_TextMode | fileusage_SavedGame, filemode_Read, 0);
	if(ref == NULL) return;

	file = glk_stream_open_file(ref, filemode_Read, 0);
	glk_fileref_destroy(ref);
	if(file == NULL) return;

	for(ct=0;ct<16;ct++)
	{
		glk_get_line_stream(file, buf, sizeof buf);
		sscanf(buf, "%d %d",&Counters[ct],&RoomSaved[ct]);
	}
	glk_get_line_stream(file, buf, sizeof buf);
	sscanf(buf, "%ld %hd %hd %d %d %hd\n",
		&BitFlags,&DarkFlag,&MyLoc,&CurrentCounter,&SavedRoom,
		&GameHeader.LightTime);
	/* Backward compatibility */
	if(DarkFlag)
		BitFlags|=(1<<15);
	for(ct=0;ct<=GameHeader.NumItems;ct++)
	{
		glk_get_line_stream(file, buf, sizeof buf);
		sscanf(buf, "%hd\n",&lo);
		Items[ct].Location=(unsigned char)lo;
	}
}

static int GetInput(int *vb, int *no)
{
	char buf[256];
	char verb[10],noun[10];
	int vc,nc;
	int num;

	do
	{
		do
		{
			Output("\nTell me what to do ? ");
			LineInput(buf, sizeof buf);
			num=sscanf(buf,"%9s %9s",verb,noun);
		}
		while(num==0||*buf=='\n');
		if(xstrcasecmp(verb, "restore") == 0)
		{
			LoadGame();
			return -1;
		}
		if(num==1)
			*noun=0;
		if(*noun==0 && strlen(verb)==1)
		{
			switch(isupper((unsigned char)*verb)?tolower((unsigned char)*verb):*verb)
			{
				case 'n':strcpy(verb,"NORTH");break;
				case 'e':strcpy(verb,"EAST");break;
				case 's':strcpy(verb,"SOUTH");break;
				case 'w':strcpy(verb,"WEST");break;
				case 'u':strcpy(verb,"UP");break;
				case 'd':strcpy(verb,"DOWN");break;
				/* Brian Howarth interpreter also supports this */
				case 'i':strcpy(verb,"INVENTORY");break;
			}
		}
		nc=WhichWord(verb,Nouns);
		/* The Scott Adams system has a hack to avoid typing 'go' */
		if(nc>=1 && nc <=6)
		{
			vc=1;
		}
		else
		{
			vc=WhichWord(verb,Verbs);
			nc=WhichWord(noun,Nouns);
		}
		*vb=vc;
		*no=nc;
		if(vc==-1)
		{
			Output("You use word(s) I don't know! ");
		}
	}
	while(vc==-1);
	strcpy(NounText,noun);	/* Needed by GET/DROP hack */

	return 0;
}

static int PerformLine(int ct)
{
	int continuation=0;
	int param[5],pptr=0;
	int act[4];
	int cc=0;
	while(cc<5)
	{
		int cv,dv;
		cv=Actions[ct].Condition[cc];
		dv=cv/20;
		cv%=20;
		switch(cv)
		{
			case 0:
				param[pptr++]=dv;
				break;
			case 1:
				if(Items[dv].Location!=CARRIED)
					return(0);
				break;
			case 2:
				if(Items[dv].Location!=MyLoc)
					return(0);
				break;
			case 3:
				if(Items[dv].Location!=CARRIED&&
					Items[dv].Location!=MyLoc)
					return(0);
				break;
			case 4:
				if(MyLoc!=dv)
					return(0);
				break;
			case 5:
				if(Items[dv].Location==MyLoc)
					return(0);
				break;
			case 6:
				if(Items[dv].Location==CARRIED)
					return(0);
				break;
			case 7:
				if(MyLoc==dv)
					return(0);
				break;
			case 8:
				if((BitFlags&(1<<dv))==0)
					return(0);
				break;
			case 9:
				if(BitFlags&(1<<dv))
					return(0);
				break;
			case 10:
				if(CountCarried()==0)
					return(0);
				break;
			case 11:
				if(CountCarried())
					return(0);
				break;
			case 12:
				if(Items[dv].Location==CARRIED||Items[dv].Location==MyLoc)
					return(0);
				break;
			case 13:
				if(Items[dv].Location==0)
					return(0);
				break;
			case 14:
				if(Items[dv].Location)
					return(0);
				break;
			case 15:
				if(CurrentCounter>dv)
					return(0);
				break;
			case 16:
				if(CurrentCounter<=dv)
					return(0);
				break;
			case 17:
				if(Items[dv].Location!=Items[dv].InitialLoc)
					return(0);
				break;
			case 18:
				if(Items[dv].Location==Items[dv].InitialLoc)
					return(0);
				break;
			case 19:/* Only seen in Brian Howarth games so far */
				if(CurrentCounter!=dv)
					return(0);
				break;
		}
		cc++;
	}
	/* Actions */
	act[0]=Actions[ct].Action[0];
	act[2]=Actions[ct].Action[1];
	act[1]=act[0]%150;
	act[3]=act[2]%150;
	act[0]/=150;
	act[2]/=150;
	cc=0;
	pptr=0;
	while(cc<4)
	{
		if(act[cc]>=1 && act[cc]<52)
		{
			Output(Messages[act[cc]]);
			Output("\n");
		}
		else if(act[cc]>101)
		{
			Output(Messages[act[cc]-50]);
			Output("\n");
		}
		else switch(act[cc])
		{
			case 0:/* NOP */
				break;
			case 52:
				if(CountCarried()==GameHeader.MaxCarry)
				{
					if(Options&YOUARE)
						Output("You are carrying too much. ");
					else
						Output("I've too much to carry! ");
					break;
				}
				Items[param[pptr++]].Location= CARRIED;
				break;
			case 53:
				Items[param[pptr++]].Location=MyLoc;
				break;
			case 54:
				MyLoc=param[pptr++];
				break;
			case 55:
				Items[param[pptr++]].Location=0;
				break;
			case 56:
				BitFlags|=1<<DARKBIT;
				break;
			case 57:
				BitFlags&=~(1<<DARKBIT);
				break;
			case 58:
				BitFlags|=(1<<param[pptr++]);
				break;
			case 59:
				Items[param[pptr++]].Location=0;
				break;
			case 60:
				BitFlags&=~(1<<param[pptr++]);
				break;
			case 61:
				if(Options&YOUARE)
					Output("You are dead.\n");
				else
					Output("I am dead.\n");
				BitFlags&=~(1<<DARKBIT);
				MyLoc=GameHeader.NumRooms;/* It seems to be what the code says! */
				break;
			case 62:
			{
				/* Bug fix for some systems - before it could get parameters wrong */
				int i=param[pptr++];
				Items[i].Location=param[pptr++];
				break;
			}
			case 63:
doneit:				Output("The game is now over.\n");
				glk_exit();
			case 64:
				break;
			case 65:
			{
				int i=0;
				int n=0;
				while(i<=GameHeader.NumItems)
				{
					if(Items[i].Location==GameHeader.TreasureRoom &&
					  *Items[i].Text=='*')
					  	n++;
					i++;
				}
				if(Options&YOUARE)
					Output("You have stored ");
				else
					Output("I've stored ");
				OutputNumber(n);
				Output(" treasures.  On a scale of 0 to 100, that rates ");
				OutputNumber((n*100)/GameHeader.Treasures);
				Output(".\n");
				if(n==GameHeader.Treasures)
				{
					Output("Well done.\n");
					goto doneit;
				}
				break;
			}
			case 66:
			{
				int i=0;
				int f=0;
				if(Options&YOUARE)
					Output("You are carrying:\n");
				else
					Output("I'm carrying:\n");
				while(i<=GameHeader.NumItems)
				{
					if(Items[i].Location==CARRIED)
					{
						if(f==1)
						{
							if (Options & TRS80_STYLE)
								Output(". ");
							else
								Output(" - ");
						}
						f=1;
						Output(Items[i].Text);
					}
					i++;
				}
				if(f==0)
					Output("Nothing");
				Output(".\n");
				break;
			}
			case 67:
				BitFlags|=(1<<0);
				break;
			case 68:
				BitFlags&=~(1<<0);
				break;
			case 69:
				GameHeader.LightTime=LightRefill;
				Items[LIGHT_SOURCE].Location=CARRIED;
				BitFlags&=~(1<<LIGHTOUTBIT);
				break;
			case 70:
				ClearScreen(); /* pdd. */
				break;
			case 71:
				SaveGame();
				break;
			case 72:
			{
				int i1=param[pptr++];
				int i2=param[pptr++];
				int t=Items[i1].Location;
				Items[i1].Location=Items[i2].Location;
				Items[i2].Location=t;
				break;
			}
			case 73:
				continuation=1;
				break;
			case 74:
				Items[param[pptr++]].Location= CARRIED;
				break;
			case 75:
			{
				int i1,i2;
				i1=param[pptr++];
				i2=param[pptr++];
				Items[i1].Location=Items[i2].Location;
				break;
			}
			case 76:	/* Looking at adventure .. */
				break;
			case 77:
				if(CurrentCounter>=0)
					CurrentCounter--;
				break;
			case 78:
				OutputNumber(CurrentCounter);
				break;
			case 79:
				CurrentCounter=param[pptr++];
				break;
			case 80:
			{
				int t=MyLoc;
				MyLoc=SavedRoom;
				SavedRoom=t;
				break;
			}
			case 81:
			{
				/* This is somewhat guessed. Claymorgue always
				   seems to do select counter n, thing, select counter n,
				   but uses one value that always seems to exist. Trying
				   a few options I found this gave sane results on ageing */
				int t=param[pptr++];
				int c1=CurrentCounter;
				CurrentCounter=Counters[t];
				Counters[t]=c1;
				break;
			}
			case 82:
				CurrentCounter+=param[pptr++];
				break;
			case 83:
				CurrentCounter-=param[pptr++];
				if(CurrentCounter< -1)
					CurrentCounter= -1;
				/* Note: This seems to be needed. I don't yet
				   know if there is a maximum value to limit too */
				break;
			case 84:
				Output(NounText);
				break;
			case 85:
				Output(NounText);
				Output("\n");
				break;
			case 86:
				Output("\n");
				break;
			case 87:
			{
				/* Changed this to swap location<->roomflag[x]
				   not roomflag 0 and x */
				int p=param[pptr++];
				int sr=MyLoc;
				MyLoc=RoomSaved[p];
				RoomSaved[p]=sr;
				break;
			}
			case 88:
				Delay(2);
				break;
			case 89:
				pptr++;
				/* SAGA draw picture n */
				/* Spectrum Seas of Blood - start combat ? */
				/* Poking this into older spectrum games causes a crash */
				break;
			default:
				fprintf(stderr,"Unknown action %d [Param begins %d %d]\n",
					act[cc],param[pptr],param[pptr+1]);
				break;
		}
		cc++;
	}
	return(1+continuation);
}


static int PerformActions(int vb,int no)
{
	static int disable_sysfunc=0;	/* Recursion lock */
	int d=BitFlags&(1<<DARKBIT);

	int ct=0;
	int fl;
	int doagain=0;
	if(vb==1 && no == -1 )
	{
		Output("Give me a direction too.");
		return(0);
	}
	if(vb==1 && no>=1 && no<=6)
	{
		int nl;
		if(Items[LIGHT_SOURCE].Location==MyLoc ||
		   Items[LIGHT_SOURCE].Location==CARRIED)
		   	d=0;
		if(d)
			Output("Dangerous to move in the dark! ");
		nl=Rooms[MyLoc].Exits[no-1];
		if(nl!=0)
		{
			MyLoc=nl;
			return(0);
		}
		if(d)
		{
			if(Options&YOUARE)
				Output("You fell down and broke your neck. ");
			else
				Output("I fell down and broke my neck. ");
			glk_exit();
		}
		if(Options&YOUARE)
			Output("You can't go in that direction. ");
		else
			Output("I can't go in that direction. ");
		return(0);
	}
	fl= -1;
	while(ct<=GameHeader.NumActions)
	{
		int vv,nv;
		vv=Actions[ct].Vocab;
		/* Think this is now right. If a line we run has an action73
		   run all following lines with vocab of 0,0 */
		if(vb!=0 && (doagain&&vv!=0))
			break;
		/* Oops.. added this minor cockup fix 1.11 */
		if(vb!=0 && !doagain && fl== 0)
			break;
		nv=vv%150;
		vv/=150;
		if((vv==vb)||(doagain&&Actions[ct].Vocab==0))
		{
			if((vv==0 && RandomPercent(nv))||doagain||
				(vv!=0 && (nv==no||nv==0)))
			{
				int f2;
				if(fl== -1)
					fl= -2;
				if((f2=PerformLine(ct))>0)
				{
					/* ahah finally figured it out ! */
					fl=0;
					if(f2==2)
						doagain=1;
					if(vb!=0 && doagain==0)
						return(0);
				}
			}
		}
		ct++;

		/* Previously this did not check ct against
		 * GameHeader.NumActions and would read past the end of
		 * Actions.  I don't know what should happen on the last
		 * action, but doing nothing is better than reading one
		 * past the end.
		 * --Chris
		 */
		if(ct <= GameHeader.NumActions && Actions[ct].Vocab!=0)
			doagain=0;
	}
	if(fl!=0 && disable_sysfunc==0)
	{
		int item;
		if(Items[LIGHT_SOURCE].Location==MyLoc ||
		   Items[LIGHT_SOURCE].Location==CARRIED)
		   	d=0;
		if(vb==10 || vb==18)
		{
			/* Yes they really _are_ hardcoded values */
			if(vb==10)
			{
				if(xstrcasecmp(NounText,"ALL")==0)
				{
					int i=0;
					int f=0;

					if(d)
					{
						Output("It is dark.\n");
						return 0;
					}
					while(i<=GameHeader.NumItems)
					{
						if(Items[i].Location==MyLoc && Items[i].AutoGet!=NULL && Items[i].AutoGet[0]!='*')
						{
							no=WhichWord(Items[i].AutoGet,Nouns);
							disable_sysfunc=1;	/* Don't recurse into auto get ! */
							PerformActions(vb,no);	/* Recursively check each items table code */
							disable_sysfunc=0;
							if(CountCarried()==GameHeader.MaxCarry)
							{
								if(Options&YOUARE)
									Output("You are carrying too much. ");
								else
									Output("I've too much to carry. ");
								return(0);
							}
							Items[i].Location= CARRIED;
							Output(Items[i].Text);
							Output(": O.K.\n");
							f=1;
						}
						i++;
					}
					if(f==0)
						Output("Nothing taken.");
					return(0);
				}
				if(no==-1)
				{
					Output("What ? ");
					return(0);
				}
				if(CountCarried()==GameHeader.MaxCarry)
				{
					if(Options&YOUARE)
						Output("You are carrying too much. ");
					else
						Output("I've too much to carry. ");
					return(0);
				}
				item=MatchUpItem(NounText,MyLoc);
				if(item==-1)
				{
					if(Options&YOUARE)
						Output("It is beyond your power to do that. ");
					else
						Output("It's beyond my power to do that. ");
					return(0);
				}
				Items[item].Location= CARRIED;
				Output("O.K. ");
				return(0);
			}
			if(vb==18)
			{
				if(xstrcasecmp(NounText,"ALL")==0)
				{
					int i=0;
					int f=0;
					while(i<=GameHeader.NumItems)
					{
						if(Items[i].Location==CARRIED && Items[i].AutoGet && Items[i].AutoGet[0]!='*')
						{
							no=WhichWord(Items[i].AutoGet,Nouns);
							disable_sysfunc=1;
							PerformActions(vb,no);
							disable_sysfunc=0;
							Items[i].Location=MyLoc;
							Output(Items[i].Text);
							Output(": O.K.\n");
							f=1;
						}
						i++;
					}
					if(f==0)
						Output("Nothing dropped.\n");
					return(0);
				}
				if(no==-1)
				{
					Output("What ? ");
					return(0);
				}
				item=MatchUpItem(NounText,CARRIED);
				if(item==-1)
				{
					if(Options&YOUARE)
						Output("It's beyond your power to do that.\n");
					else
						Output("It's beyond my power to do that.\n");
					return(0);
				}
				Items[item].Location=MyLoc;
				Output("O.K. ");
				return(0);
			}
		}
	}
	return(fl);
}

glkunix_argumentlist_t glkunix_arguments[] =
{
	{ "-y",		glkunix_arg_NoValue,		"-y		Generate 'You are', 'You are carrying' type messages for games that use these instead (eg Robin Of Sherwood)" },
	{ "-i",		glkunix_arg_NoValue,		"-i		Generate 'I am' type messages (default)" },
	{ "-d",		glkunix_arg_NoValue,		"-d		Debugging info on load " },
	{ "-s",		glkunix_arg_NoValue,		"-s		Generate authentic Scott Adams driver light messages rather than other driver style ones (Light goes out in n turns..)" },
	{ "-t",		glkunix_arg_NoValue,		"-t		Generate TRS80 style display (terminal width is 64 characters; a line <-----------------> is displayed after the top stuff; objects have periods after them instead of hyphens" },
	{ "-p",		glkunix_arg_NoValue,		"-p		Use for prehistoric databases which don't use bit 16" },
	{ "-w",		glkunix_arg_NoValue,		"-w		Disable upper window" },
	{ "",		glkunix_arg_ValueFollows,	"filename	file to load" },

	{ NULL, glkunix_arg_End, NULL }
};

static const char *game_file;

int glkunix_startup_code(glkunix_startup_t *data)
{
	int argc = data->argc;
	char **argv = data->argv;

	if(argc < 1)
		return 0;

	while(argv[1])
	{
		if(*argv[1]!='-')
			break;
		switch(argv[1][1])
		{
			case 'y':
				Options|=YOUARE;
				break;
			case 'i':
				Options&=~YOUARE;
				break;
			case 'd':
				Options|=DEBUGGING;
				break;
			case 's':
				Options|=SCOTTLIGHT;
				break;
			case 't':
				Options|=TRS80_STYLE;
				break;
			case 'p':
				Options|=PREHISTORIC_LAMP;
				break;
			case 'w':
				split_screen = 0;
				break;
		}
		argv++;
		argc--;
	}

#ifdef GARGLK
	garglk_set_program_name("ScottFree 1.14");
	garglk_set_program_info(
		"ScottFree 1.14 by Alan Cox\n"
		"Glk port by Chris Spiegel\n");
#endif

	if(argc==2)
	{
		game_file = argv[1];
#ifdef GARGLK
		const char *s;
		if((s = strrchr(game_file, '/')) != NULL || (s = strrchr(game_file, '\\')) != NULL)
		{
			garglk_set_story_name(s + 1);
		}
		else
		{
			garglk_set_story_name(game_file);
		}
#endif
	}

	return 1;
}

void glk_main(void)
{
	FILE *f;
	int vb,no;

	Bottom = glk_window_open(0, 0, 0, wintype_TextBuffer, 1);
	if(Bottom == NULL)
		glk_exit();
	glk_set_window(Bottom);

	if(game_file == NULL)
		Fatal("No game provided");

	f = fopen(game_file, "r");
	if(f==NULL)
		Fatal("Cannot open game");

	if (Options & TRS80_STYLE)
	{
		Width = 64;
		TopHeight = 11;
	}
	else
	{
		Width = 80;
		TopHeight = 10;
	}

	if(split_screen)
	{
		Top = glk_window_open(Bottom, winmethod_Above | winmethod_Fixed, TopHeight, wintype_TextGrid, 0);
		if(Top == NULL)
		{
			split_screen = 0;
			Top = Bottom;
		}
	}
	else
	{
		Top = Bottom;
	}

	Output("\
Scott Free, A Scott Adams game driver in C.\n\
Release 1.14, (c) 1993,1994,1995 Swansea University Computer Society.\n\
Distributed under the GNU software license\n\n");
	LoadDatabase(f,(Options&DEBUGGING)?1:0);
	fclose(f);
	srand(time(NULL));
	while(1)
	{
		glk_tick();

		PerformActions(0,0);

		Look();

		if(GetInput(&vb,&no) == -1)
			continue;
		switch(PerformActions(vb,no))
		{
			case -1:Output("I don't understand your command. ");
				break;
			case -2:Output("I can't do that yet. ");
				break;
		}
		/* Brian Howarth games seem to use -1 for forever */
		if(Items[LIGHT_SOURCE].Location/*==-1*/!=DESTROYED && GameHeader.LightTime!= -1)
		{
			GameHeader.LightTime--;
			if(GameHeader.LightTime<1)
			{
				BitFlags|=(1<<LIGHTOUTBIT);
				if(Items[LIGHT_SOURCE].Location==CARRIED ||
					Items[LIGHT_SOURCE].Location==MyLoc)
				{
					if(Options&SCOTTLIGHT)
						Output("Light has run out! ");
					else
						Output("Your light has run out. ");
				}
				if(Options&PREHISTORIC_LAMP)
					Items[LIGHT_SOURCE].Location=DESTROYED;
			}
			else if(GameHeader.LightTime<25)
			{
				if(Items[LIGHT_SOURCE].Location==CARRIED ||
					Items[LIGHT_SOURCE].Location==MyLoc)
				{

					if(Options&SCOTTLIGHT)
					{
						Output("Light runs out in ");
						OutputNumber(GameHeader.LightTime);
						Output(" turns. ");
					}
					else
					{
						if(GameHeader.LightTime%5==0)
							Output("Your light is growing dim. ");
					}
				}
			}
		}
	}
}
