/*
	HEGLK.C

	Glk interface functions for the Hugo Engine

	Copyright (c) 1999-2006 by Kent Tessman

	The colour handling (see COLOURS below) is adapted from the
	Spatterlight port, hecugel.c, by Petter Sjölund.  It uses the
	Gargoyle text extensions (GLK_MODULE_GARGLKTEXT); with another
	Glk library the colour calls compile to nothing and the port
	behaves as before.
*/


#include "heheader.h"
#include "glk.h"


/* Glk main window: */
static winid_t mainwin = NULL;

/* Usually the statusline window: */
static winid_t secondwin = NULL;

/* In case we try to print positioned text to the main window,
   as in a menu: */
static winid_t auxwin = NULL;

/* A virtual window that points to one of the three above: */
static winid_t currentwin = NULL;

/* The height secondwin was last given, in lines */
static int secondwin_bottom = 0;

#define CHARWIDTH 1
int in_valid_window = false;
int glk_current_font;
char just_cleared_screen = false;

#define STAT_UNAVAILABLE (-1)

static void heglk_init_colors(void);
static void heglk_apply_colors(void);
static void heglk_clear_textwin(winid_t win);
static void heglk_paint_grid(winid_t win);
static void heglk_paint_auxwin(void);
static void heglk_forget_colors(winid_t win);
static void heglk_seed_secondwin(void);
static void heglk_repaint_mainwin(void);
static void heglk_resync_mainwin(void);

#include "hemedia.c"

/* glk_main

	The entry point for Glk:  starts up the Hugo Engine.
	The arguments glk_argc and glk_argv must be made up before
	glk_main() is called.
*/

void glk_main(void)
{
	/* Open the main window... */
	mainwin = glk_window_open(0, 0, 0, wintype_TextBuffer, 1);

	/* ...and set it up for default output */
	glk_set_window(currentwin = mainwin);

	/* It's possible that the main window failed to open. There's
	   nothing we can do without it, so exit */
	if (!mainwin)
		return; 

	heglk_init_colors();

	he_main(0, NULL);	/* no argc, argv */
}


/*
 * MEMORY ALLOCATION:
 *
 */

void *hugo_blockalloc(long num)
{
	return malloc(num * sizeof(char));
}

void hugo_blockfree(void *block)
{
	free(block);                           /* i.e. free() */
}


/*
 * FILE MANAGEMENT:
 *
 */

/* Glk Hugo doesn't need these; they're handled by the Glk library:
void hugo_splitpath(char *path, char *drive, char *dir, char *fname, char *ext)
{}

void hugo_makepath(char *path, char *drive, char *dir, char *fname, char *ext)
{}

void hugo_getfilename(char *a, char *b)
{}

int hugo_overwrite(char *f)
{}
*/

void hugo_closefiles()
{
	/* Glk closes all files at glk_exit() */
}


/*
 * KEYBOARD INPUT:
 *
 */

/* hugo_getkey */

int hugo_getkey(void)
{
	/* Not needed here--single-character events are handled
	   solely by hugo_waitforkey(), below */

	return 0;
}


/* hugo_getline

	Gets a line of input from the keyboard, storing it in <buffer>.
*/

void hugo_getline(char *prmpt)
{
	event_t ev;
	char gotline = 0;

	/* Just in case we try to get line input from a Glk-illegal
	   window that hasn't been created, switch as a failsafe
	   to mainwin
	*/
	if (currentwin==NULL)
		glk_set_window(currentwin = mainwin);

	/* Print prompt */
	heglk_apply_colors();
	glk_put_string(prmpt);

	/* Request line input */
	glk_request_line_event(currentwin, buffer, MAXBUFFER, 0);

        while (!gotline)
	{
		/* Grab an event */
		glk_select(&ev);

		switch (ev.type)
		{
 			case evtype_LineInput:
				/* (Will always be currentwin, but anyway) */
				if (ev.win==currentwin)
				{
					gotline = true;
				}
				break;
		}
        }
        
	/* The line we have received in commandbuf is not null-terminated */
	buffer[ev.val1] = '\0';	/* i.e., the length */

	/* Copy the input to the script file (if open) */
	if (script)
	{
		/* This looks inefficient, but it's necessary because
		   of the way Glk functions are mapped by stdio
		*/
		fprintf(script, "%s", prmpt);
		fprintf(script, "%s", buffer);
		fprintf(script, "%s", "\n");
	}
}


/* hugo_waitforkey

	Provided to be replaced by multitasking systems where cycling while
	waiting for a keystroke may not be such a hot idea.
*/

int hugo_waitforkey(void)
{
	event_t ev;
	char gotchar = 0;

	/* Just in case we try to get key input from a Glk-illegal
	   window that hasn't been created, switch as a failsafe
	   to mainwin
	*/
	if (currentwin==NULL)
		glk_set_window(currentwin = mainwin);

#if defined (NO_KEYPRESS_CURSOR)
	if (currentwin!=mainwin)
	{
		glk_window_move_cursor(currentwin, currentpos/CHARWIDTH, currentline-1);
		hugo_print("*");
		glk_window_move_cursor(currentwin, currentpos/CHARWIDTH, currentline-1);
	}
#endif
	
	glk_request_char_event(currentwin);

        while (!gotchar)
	{
		/* Grab an event */
		glk_select(&ev);
            
		switch (ev.type)
		{
 			case evtype_CharInput:
				/* (Will always be mainwin, but anyway) */
				if (ev.win==currentwin)
				{
					gotchar = true;
				}
				break;
		}
        }

	/* Convert Glk special keycodes: */
	switch (ev.val1)
	{
		case keycode_Left:	ev.val1 = 8;	break;
		case keycode_Right:	ev.val1 = 21;	break;
		case keycode_Up:	ev.val1 = 11;	break;
		case keycode_Down:	ev.val1 = 10;	break;
		case keycode_Return:	ev.val1 = 13;	break;
		case keycode_Escape:	ev.val1 = 27;	break;
	}

#if defined (NO_KEYPRESS_CURSOR)
	if (currentwin!=mainwin)
	{
		glk_window_move_cursor(currentwin, currentpos/CHARWIDTH, currentline-1);
		hugo_print(" ");
		glk_window_move_cursor(currentwin, currentpos/CHARWIDTH, currentline-1);
	}
#endif

	return ev.val1;
}


/* hugo_iskeywaiting

	Returns true if a keypress is waiting to be retrieved.
*/

int hugo_iskeywaiting(void)
{
	var[system_status] = STAT_UNAVAILABLE;
	return 0;
}


/* hugo_timewait

    Waits for 1/n seconds.  Returns false if waiting is unsupported.
*/

int hugo_timewait(int n)
{
	glui32 millisecs;
	event_t ev;
    
	if (!glk_gestalt(gestalt_Timer, 0))
		return false;
	if (n==0) return true;

        
	millisecs = 1000 / n;
	if (millisecs == 0)
		millisecs = 1;

	// For the time being, we're going to disallow
	// millisecond delays in Glk (1) because there's no
	// point, and (2) so that we can tell we're running
	// under Glk.
	if (millisecs < 1000) return false;

	glk_request_timer_events(millisecs);
	while (1)
	{
		glk_select(&ev);
		if (ev.type == evtype_Timer)
			break;
	}
	glk_request_timer_events(0);
	return true;
}


/*
 * DISPLAY CONTROL:
 *
 */

void hugo_init_screen(void)
{
/* Does whatever has to be done to initially set up the display. */

	/* By setting the width and height so high, we're basically
	   forcing the Glk library to deal with text-wrapping and
	   page ends
	*/
	SCREENWIDTH = 0x7fff;
	SCREENHEIGHT = 0x7fff;
	FIXEDCHARWIDTH = 1;
	FIXEDLINEHEIGHT = 1;

	hugo_settextwindow(1, 1,
		SCREENWIDTH/FIXEDCHARWIDTH, SCREENHEIGHT/FIXEDLINEHEIGHT);
}


void hugo_cleanup_screen(void)
{
/* Does whatever has to be done to clean up the display pre-termination. */
}


#if !defined (PRINTFATALERROR_SUPPLIED)
void heglk_printfatalerror(char *err)
{
	static winid_t win = NULL;
	
	if (!win)
	{
		winid_t rootwin = glk_window_get_root();
		if (!rootwin)
			win = glk_window_open(0, 0, 0, wintype_TextBuffer, 0);
		else
			win = glk_window_open(rootwin, winmethod_Below | winmethod_Fixed, 
				3, wintype_TextBuffer, 0);
	}
	
	if (win)
	{
		glk_put_string_stream(glk_window_get_stream(win), err);
	}
}
#endif	/* PRINTFATALERROR_SUPPLIED */


void hugo_clearfullscreen(void)
{
/* Clears everything on the screen, moving the cursor to the top-left
   corner of the screen */

	heglk_clear_textwin(mainwin);
	if (secondwin) heglk_clear_textwin(secondwin);
	if (auxwin) heglk_clear_textwin(auxwin);
	if (currentwin==mainwin) heglk_resync_mainwin();

	/* Must be set: */
	currentpos = 0;
	currentline = 1;

	if (!inwindow) just_cleared_screen = true;
}


void hugo_clearwindow(void)
{
/* Clears the currently defined window, moving the cursor to the top-left
   corner of the window */

	/* If the engine thinks we're in a window, but Glk was
	   unable to comply, don't clear the window, because it's
	   not really a window
	*/
	if (inwindow && currentwin==mainwin) return;
	if (currentwin==NULL) return;

	/* If we're in a fixed-font (i.e., textgrid) auxiliary
	   window when we call for a clear, close auxwin and reset
	   the current window to mainwin.  The screen the menu was
	   drawn over is what gets cleared.
	*/
	if (auxwin)
	{
		stream_result_t sr;

		glk_window_close(auxwin, &sr);
		auxwin = NULL;
		glk_set_window(currentwin = mainwin);
		heglk_resync_mainwin();
	}

	heglk_clear_textwin(currentwin);

	/* Must be set: */
	currentpos = 0;
	currentline = 1;

	if (!inwindow) just_cleared_screen = true;
}


void hugo_settextmode(void)
{
/* This function does whatever is necessary to set the system up for
   a standard text display */

	charwidth = FIXEDCHARWIDTH;
	lineheight = FIXEDLINEHEIGHT;

	return;
}


void hugo_settextwindow(int left, int top, int right, int bottom)
{
	/* Hugo's arbitrarily positioned windows don't currently
	   mesh with what Glk has to offer, so we have to ignore any
	   non-Glk-ish Windows and just maintain the current
	   parameters
	*/
	if ((top!=1 || bottom>=physical_windowbottom/FIXEDLINEHEIGHT+1)
		/* Pre-v2.4 didn't support proper windowing */
		&& (game_version>=24 || !inwindow))
	{
		in_valid_window = false;
		
		/* Glk-illegal floating window; setting currentwin
		   to NULL will tell hugo_print() not to print in it:
		*/
		if (bottom<physical_windowbottom/FIXEDLINEHEIGHT+1)
		{
			currentwin = NULL;
			glk_set_window(mainwin);
			return;
		}
		else
		{
			glk_set_window(currentwin = mainwin);
			heglk_resync_mainwin();
		}
	}

	/* Otherwise this is a valid window (positioned along the
	   top of the screen a la a status window), so... */
	else
	{
		/* Arbitrary height of 4 lines for pre-v2.4 windows */
		if (game_version < 24) bottom = 4;

		/* ...either create a new window if none exists... */
		if (!secondwin)
		{
			secondwin = glk_window_open(mainwin,
				winmethod_Above | winmethod_Fixed,
				bottom,
				wintype_TextGrid,
				0);
			heglk_seed_secondwin();
		}

		/* ...or resize the existing one if necessary */
		else if (bottom!=secondwin_bottom)
		{
			winid_t p;

			p  = glk_window_get_parent(secondwin);
			glk_window_set_arrangement(p, 
				winmethod_Above | winmethod_Fixed,
				bottom,
				secondwin);
			/* Rearranging a text grid resets its colours */
			heglk_seed_secondwin();
		}

		if (secondwin)
		{
			if (game_version < 24)
				heglk_clear_textwin(secondwin);

			glk_set_window(currentwin = secondwin);
			in_valid_window = true;
			secondwin_bottom = bottom;
		}
		else
		{
			currentwin = NULL;
			glk_set_window(mainwin);
			secondwin_bottom = 0;
			return;
		}
	}

	physical_windowleft = (left-1)*FIXEDCHARWIDTH;
	physical_windowtop = (top-1)*FIXEDLINEHEIGHT;
	physical_windowright = right*FIXEDCHARWIDTH-1;
	physical_windowbottom = bottom*FIXEDLINEHEIGHT-1;
	physical_windowwidth = (right-left+1)*FIXEDCHARWIDTH;
	physical_windowheight = (bottom-top+1)*FIXEDLINEHEIGHT;
}


/* heglk_get_linelength

	Specially accommodated in GetProp() in heobject.c.
	While the engine thinks that the linelength is 0x7fff,
	this tells things like the display object the actual
	length.  (Defined as ACTUAL_LINELENGTH in heheader.h.)
*/

int heglk_get_linelength(void)
{
	static glui32 width;

	/* Try to use whatever fixed-width linelength is available */
	if (secondwin)
		glk_window_get_size(secondwin, &width, NULL);
	else if (auxwin)
		glk_window_get_size(auxwin, &width, NULL);

	/* Otherwise try to approximate it by the proportionally
	   spaced linelength
	*/
	else
		glk_window_get_size(mainwin, &width, NULL);

	/* -1 to override automatic line wrapping */
	return width-1;
}


/* heglk_get_screenheight

	Similar to heglk_get_linelength().  (Defined as
	ACTUAL_SCREENHEIGHT in heheader.h.)
*/

int heglk_get_screenheight(void)
{
	static glui32 height = 0, mainheight = 0;

	if (secondwin)
		glk_window_get_size(secondwin, NULL, &height);
	else if (auxwin)
		glk_window_get_size(auxwin, NULL, &height);

	glk_window_get_size(mainwin, NULL, &mainheight);

	return height+mainheight;
}


void hugo_settextpos(int x, int y)
{
/* The top-left corner of the current active window is (1, 1). */

	if (currentwin==NULL) return;

	/* Try to determine if we're trying to position fixed-width
	   text in the main window, as in a menu, for example
	*/
	if (!just_cleared_screen && !inwindow &&
		!(glk_current_font & PROP_FONT)
		&& y!=1			/* not just cls */
		&& y < SCREENHEIGHT-0x0f)	/* 0x0f is arbitrary */
	{
		/* See if we're already in the auxiliary window */
		if (currentwin!=auxwin)
		{
			/* If not, create it, making it 100% of
			   mainwin's height
			*/
			if (auxwin==NULL)
			{
				auxwin = glk_window_open(mainwin,
					winmethod_Below | winmethod_Proportional,
					100,
					wintype_TextGrid,
					0);
			}
			else
				glk_window_clear(auxwin);

			heglk_paint_auxwin();
			glk_set_window(currentwin = auxwin);
		}
	}

	/* On the other hand, if we were in a textgrid window and
	   no longer need to be, get out
	*/
	else if (auxwin)
	{
		stream_result_t sr;

		/* Close auxwin */
		glk_window_close(auxwin, &sr);
		auxwin = NULL;

		/* Clear the screen (both windows) */
		heglk_clear_textwin(mainwin);
		heglk_clear_textwin(secondwin);

		glk_set_window(currentwin = mainwin);
		heglk_resync_mainwin();
	}

	just_cleared_screen = false;

	/* Can only move the Glk cursor in a textgrid window */
	if (currentwin!=mainwin)
		glk_window_move_cursor(currentwin, x-1, y-1);

	/* Must be set: */
	currentline = y;
	currentpos = (x-1)*CHARWIDTH;   /* Note:  zero-based */
}


void hugo_print(char *a)
{
/* Essentially the same as printf() without formatting, since printf()
   generally doesn't take into account color setting, font changes,
   windowing, etc.

   The newline character '\n' must be explicitly included at the end of
   a line in order to produce a linefeed.  The new cursor position is set
   to the end of this printed text.  Upon hitting the right edge of the
   screen, the printing position wraps to the start of the next line.
*/
	static char just_printed_linefeed = false;

	/* Can't print in a Glk-illegal window since it hasn't been
	   created
	*/
	if (currentwin==NULL) return;

	if (a[0]=='\n')
	{
		if (!just_printed_linefeed)
		{
			glk_put_string("\n");
		}
		else
			just_printed_linefeed = false;
	}
	else if (a[0]=='\r')
	{
		if (!just_printed_linefeed)
		{
			glk_put_string("\n");
			just_printed_linefeed = true;
		}
		else
			just_printed_linefeed = false;
	}
	else
	{
		heglk_apply_colors();
		glk_put_string(a);
		just_printed_linefeed = false;
	}
}


void hugo_scrollwindowup()
{
	/* Glk should look after this for us */
}


void hugo_font(int f)
{
	static char using_prop_font = false;

/* The <f> argument is a mask containing any or none of:
   BOLD_FONT, UNDERLINE_FONT, ITALIC_FONT, PROP_FONT.
*/
	glk_current_font = f;

	glk_set_style(style_Normal);

	if (f & BOLD_FONT)
		glk_set_style(style_Subheader);

	if (f & UNDERLINE_FONT)
		glk_set_style(style_Emphasized);

	if (f & ITALIC_FONT)
		glk_set_style(style_Emphasized);

	if (f & PROP_FONT)
		using_prop_font = true;

/* Have to comment this out, it seems, because it will mess up the
   alignment of the input in the main window
	if (!(f & PROP_FONT))
		glk_set_style(style_Preformatted);
*/

/* Workaround to decide if we have to open auxwin for positioned
   non-proportional text:
*/
	if (!(f & PROP_FONT))
	{
		/* If at top of screen, and changing to a fixed-
		   width font (a situation which wouldn't normally
		   be adjusted for by hugo_settextpos())
		*/
		if (!inwindow && currentline==1 && currentpos==0 && using_prop_font)
		{
			just_cleared_screen = false;
			hugo_settextpos(1, 2);
			glk_window_move_cursor(currentwin, 0, 0);
		}
	}
}


/*
 * COLOURS
 *
 * The engine passes hugo_settextcolor() and hugo_setbackcolor() an
 * index: 0-15 are the Hugo palette, 16-19 the four defaults (text,
 * background, statusline text, statusline background), and 20 means
 * "match the foreground".  heheader.h gives DEF_FCOLOR and friends
 * palette values for a port that has to pick real colours; the engine
 * itself works with the indices (hemisc.c starts out with fcolor = 16
 * and bgcolor = 17), so that is what arrives here.
 *
 * Each window keeps its own colours.  The engine does not send the
 * main window's colours again when a window block ends, so what was
 * set inside the status window must not leak into the main window.
 * A new status window starts out in the statusline text colour on
 * whatever the screen was last cleared to, and a menu grid in the main
 * window's colours.  Colours set while the engine is in a window Glk
 * cannot show are dropped.
 *
 * Text is coloured with Gargoyle's zcolors.  The main text default on
 * the main background default is passed on as zcolor_Default, so that
 * the library's theme decides what it looks like.  The statusline
 * defaults are the theme reversed, as Spatterlight draws them; they
 * and the other pairs of defaults are sent as RGB, because Gargoyle
 * resolves default colours through the ones last set on any stream.
 *
 * An explicit background has to cover the whole window and not just the
 * text.  A text grid is filled with spaces in that colour when it is
 * cleared.  A text buffer gets the colour as a stylehint and is reopened,
 * which is only done when it is being cleared anyway, or before anything
 * has been printed in it (for a game that sets its colours and starts
 * printing without clearing the screen first).
 */

#define HUGO_BLACK		0
#define HUGO_WHITE		7
#define HUGO_DEFAULT_FG		16
#define HUGO_DEFAULT_BG		17
#define HUGO_DEFAULT_SLFG	18
#define HUGO_DEFAULT_SLBG	19
#define HUGO_MATCH_FG		20

/* The Hugo palette, as RGB */
static const glui32 hugo_rgb[16] =
{
	0x000000, 0x00007f, 0x007f00, 0x007f7f,
	0x7f0000, 0x7f007f, 0x7f5f00, 0xcfcfcf,
	0x3f3f3f, 0x0000ff, 0x00ff00, 0x00ffff,
	0xff0000, 0xff00ff, 0xffff00, 0xffffff
};

/* The theme's text and background colours, measured once before any
   stylehint has been set */
static glui32 theme_fg = 0x000000, theme_bg = 0xffffff;

struct wincolors
{
	int fg, bg;		/* the colours the engine last set in it */
	int paper;		/* palette index the window is painted in,
				   or -1 for the theme's background */
	int printed;		/* something has been printed in it since
				   it was last cleared */
	int sent;		/* the zcolors below have been handed to it */
	glui32 sent_fg, sent_bg;
};

/* The palette index the screen was last cleared to, or -1 for the
   theme's background:  a window opened over it starts on that paint
*/
static int screen_bg = -1;

enum { WIN_MAIN, WIN_SECOND, WIN_AUX, WIN_COUNT };
static struct wincolors wincolors[WIN_COUNT];

struct zcolors
{
	glui32 fg, bg;
};


static struct wincolors *heglk_wincolors(winid_t win)
{
	if (win==NULL) return NULL;
	if (win==mainwin) return &wincolors[WIN_MAIN];
	if (win==secondwin) return &wincolors[WIN_SECOND];
	if (win==auxwin) return &wincolors[WIN_AUX];
	return NULL;
}


static void heglk_init_colors(void)
{
	glui32 val;
	int i;

	for (i=0; i<WIN_COUNT; i++)
	{
		wincolors[i].fg = (i==WIN_SECOND) ? HUGO_DEFAULT_SLFG : HUGO_DEFAULT_FG;
		wincolors[i].bg = (i==WIN_SECOND) ? HUGO_DEFAULT_SLBG : HUGO_DEFAULT_BG;
		wincolors[i].paper = -1;
		wincolors[i].printed = false;
		wincolors[i].sent = false;
	}

	if (glk_style_measure(mainwin, style_Normal, stylehint_TextColor, &val))
		theme_fg = val;
	if (glk_style_measure(mainwin, style_Normal, stylehint_BackColor, &val))
		theme_bg = val;
}


static int heglk_is_default(int c)
{
	return c>=HUGO_DEFAULT_FG && c<=HUGO_DEFAULT_SLBG;
}


/* The paint a window cleared now gets:  its explicit background, or
   the theme's
*/

static int heglk_paper_of(struct wincolors *wc)
{
	return heglk_is_default(wc->bg) ? -1 : wc->bg;
}


/* An index as RGB.  The statusline defaults are the theme reversed. */

static glui32 heglk_rgb(int c)
{
	switch (c)
	{
		case HUGO_DEFAULT_FG:
		case HUGO_DEFAULT_SLBG:
			return theme_fg;
		case HUGO_DEFAULT_BG:
		case HUGO_DEFAULT_SLFG:
			return theme_bg;
	}
	if (c>=0 && c<16) return hugo_rgb[c];
	return theme_fg;
}


/* The zcolors for text in FG on BG, in a window painted PAPER */

static struct zcolors heglk_zcolors(int fg, int bg, int paper)
{
	struct zcolors z;
	glui32 shown_fg, shown_bg;

	z.fg = zcolor_Default;
	z.bg = zcolor_Default;

	if (fg==HUGO_DEFAULT_FG && bg==HUGO_DEFAULT_BG)
	{
		/* The theme itself, left to the library so that its styles
		   keep their own colours
		*/
	}
	else if (heglk_is_default(fg) && heglk_is_default(bg))
	{
		/* Any other pair of defaults, such as the statusline's, or
		   the main pair the other way round for a menu's highlight
		   bar, is given as RGB:  Gargoyle resolves default colours
		   through the last ones set on any stream, so reverse
		   video on defaults would follow the main window's colours
		*/
		z.fg = heglk_rgb(fg);
		z.bg = heglk_rgb(bg);
	}
	else
	{
		if (!heglk_is_default(fg))
			z.fg = hugo_rgb[fg];
		else if (fg!=HUGO_DEFAULT_FG)
			z.fg = heglk_rgb(fg);

		if (!heglk_is_default(bg))
			z.bg = hugo_rgb[bg];
		else if (bg!=HUGO_DEFAULT_BG)
			z.bg = heglk_rgb(bg);
	}

	/* Default text in a painted window sits on the paint, not on
	   the theme's background
	*/
	if (z.bg==zcolor_Default && paper>=0)
		z.bg = hugo_rgb[paper];

	/* Black on black would vanish.  Spatterlight shows it in white,
	   and so do we.
	*/
	shown_fg = (z.fg==zcolor_Default) ? theme_fg : z.fg;
	shown_bg = (z.bg==zcolor_Default) ? theme_bg : z.bg;
	if (shown_fg==hugo_rgb[HUGO_BLACK] && shown_bg==hugo_rgb[HUGO_BLACK])
		z.fg = hugo_rgb[HUGO_WHITE];

	return z;
}


#if defined (GLK_MODULE_GARGLKTEXT)
static void heglk_send_colors(winid_t win, struct zcolors z)
{
	struct wincolors *wc = heglk_wincolors(win);
	strid_t str = glk_window_get_stream(win);

	if (wc==NULL) return;

	if (!wc->sent || z.fg!=wc->sent_fg || z.bg!=wc->sent_bg)
		garglk_set_zcolors_stream(str, z.fg, z.bg);

	wc->sent = true;
	wc->sent_fg = z.fg;
	wc->sent_bg = z.bg;

	/* Gargoyle keeps the colours last set on any stream as the paper
	   of every text buffer and of the border, so the main window has
	   to be given its own again after this
	*/
	if (win!=mainwin)
		wincolors[WIN_MAIN].sent = false;
}
#endif


/* Back in the main window after another one has been written to:
   make its colours the ones the library shows
*/

static void heglk_resync_mainwin(void)
{
#if defined (GLK_MODULE_GARGLKTEXT)
	struct wincolors *wc = &wincolors[WIN_MAIN];

	if (mainwin && !wc->sent)
		heglk_send_colors(mainwin, heglk_zcolors(wc->fg, wc->bg, wc->paper));
#endif
}


/* Called before text goes to currentwin:  hand it its colours, if they
   are not what it last got.  Colours set before the first text in a
   window paint the window as well.
*/

static void heglk_apply_colors(void)
{
	struct wincolors *wc = heglk_wincolors(currentwin);

	if (wc==NULL) return;

	if (!wc->printed && heglk_paper_of(wc)!=wc->paper)
	{
		if (currentwin==mainwin)
			heglk_repaint_mainwin();
		else
			heglk_paint_grid(currentwin);
		wc = heglk_wincolors(currentwin);
		if (wc==NULL) return;
	}

#if defined (GLK_MODULE_GARGLKTEXT)
	heglk_send_colors(currentwin, heglk_zcolors(wc->fg, wc->bg, wc->paper));
#endif
	wc->printed = true;
}


/* The window has been cleared or (re)opened:  the library has reset
   its colours
*/

static void heglk_forget_colors(winid_t win)
{
	struct wincolors *wc = heglk_wincolors(win);

	if (wc==NULL) return;
	wc->sent = false;
	wc->printed = false;
}


/* A status window has just been opened or resized:  it starts in the
   statusline's text colour on whatever the screen was last cleared to
*/

static void heglk_seed_secondwin(void)
{
	struct wincolors *wc = &wincolors[WIN_SECOND];

	wc->fg = HUGO_DEFAULT_SLFG;
	wc->bg = (screen_bg>=0) ? screen_bg : HUGO_DEFAULT_SLBG;
	heglk_forget_colors(secondwin);
}


/* Fill a text grid with spaces in its colours, so that an explicit
   background, or the reversed theme of the statusline, covers all of it
*/

static void heglk_paint_grid(winid_t win)
{
	struct wincolors *wc = heglk_wincolors(win);
	struct zcolors z;
	glui32 width, height, n;
	strid_t str;

	if (wc==NULL) return;

	wc->paper = heglk_paper_of(wc);
	wc->printed = false;

	z = heglk_zcolors(wc->fg, wc->bg, -1);
	if (z.bg==zcolor_Default)
		return;		/* the theme's background: it is that already */

	glk_window_get_size(win, &width, &height);
	str = glk_window_get_stream(win);
#if defined (GLK_MODULE_GARGLKTEXT)
	heglk_send_colors(win, z);
#endif
	for (n=0; n<width*height; n++)
		glk_put_char_stream(str, ' ');
	glk_window_move_cursor(win, 0, 0);
}


/* A menu grid opened over the main window is painted like it */

static void heglk_paint_auxwin(void)
{
	struct wincolors *aux = &wincolors[WIN_AUX];
	struct wincolors *main = &wincolors[WIN_MAIN];

	aux->fg = main->fg;
	aux->bg = (main->paper>=0) ? main->paper : main->bg;
	heglk_forget_colors(auxwin);
	heglk_paint_grid(auxwin);
}


/* Set the stylehints for a text buffer painted PAPER, for the next one
   to be opened
*/

static void heglk_paper_hints(struct wincolors *wc, int paper)
{
	struct zcolors z = heglk_zcolors(wc->fg, wc->bg, paper);
	glui32 s;

	for (s=0; s<style_NUMSTYLES; s++)
	{
		if (paper>=0)
			glk_stylehint_set(wintype_TextBuffer, s, stylehint_BackColor, hugo_rgb[paper]);
		else
			glk_stylehint_clear(wintype_TextBuffer, s, stylehint_BackColor);
	}

	/* The caret and the more prompt follow Normal's text colour */
	if (paper>=0 && z.fg!=zcolor_Default)
		glk_stylehint_set(wintype_TextBuffer, style_Normal, stylehint_TextColor, z.fg);
	else
		glk_stylehint_clear(wintype_TextBuffer, style_Normal, stylehint_TextColor);
}


/* Reopen the main window painted in its background.  What was in it
   goes, so this is only done when it is being cleared, or before
   anything has been printed in it.
*/

static void heglk_repaint_mainwin(void)
{
	struct wincolors *wc = &wincolors[WIN_MAIN];
	stream_result_t sr;
	int paper = heglk_paper_of(wc);
	int was_current = (currentwin==mainwin);
	winid_t newwin;

	heglk_paper_hints(wc, paper);

	if (auxwin)
	{
		if (currentwin==auxwin) was_current = true;
		glk_window_close(auxwin, &sr);
		auxwin = NULL;
	}

	glk_window_close(mainwin, &sr);

	if (secondwin)
	{
		/* Below the status window, which stays the key window
		   with its fixed height
		*/
		newwin = glk_window_open(secondwin,
			winmethod_Below | winmethod_Proportional, 50,
			wintype_TextBuffer, 1);
		if (newwin)
			glk_window_set_arrangement(glk_window_get_parent(newwin),
				winmethod_Above | winmethod_Fixed,
				secondwin_bottom, secondwin);
	}
	else
		newwin = glk_window_open(0, 0, 0, wintype_TextBuffer, 1);

	mainwin = newwin;
	if (mainwin==NULL)
		glk_exit();

	wc->paper = paper;
	heglk_forget_colors(mainwin);

	if (was_current)
		currentwin = mainwin;
	glk_set_window(currentwin ? currentwin : mainwin);
}


/* Clear a text window, repainting it if its background has changed */

static void heglk_clear_textwin(winid_t win)
{
	if (win==NULL) return;

	if (win==mainwin)
	{
		if (heglk_paper_of(&wincolors[WIN_MAIN])!=wincolors[WIN_MAIN].paper)
			heglk_repaint_mainwin();
		else
		{
			glk_window_clear(mainwin);
			heglk_forget_colors(mainwin);
		}
		if (!inwindow)
			screen_bg = wincolors[WIN_MAIN].paper;
	}
	else
	{
		glk_window_clear(win);
		heglk_forget_colors(win);
		heglk_paint_grid(win);
	}
}


void hugo_settextcolor(int c)           /* foreground (print) color */
{
	struct wincolors *wc = heglk_wincolors(currentwin);

	if (wc==NULL) return;
	if (c==HUGO_MATCH_FG) return;
	if (c<0 || c>HUGO_DEFAULT_SLBG) c = HUGO_DEFAULT_FG;
	wc->fg = c;
}


void hugo_setbackcolor(int c)           /* background color */
{
	struct wincolors *wc = heglk_wincolors(currentwin);

	if (wc==NULL) return;
	if (c==HUGO_MATCH_FG) c = wc->fg;
	if (c<0 || c>HUGO_DEFAULT_SLBG) c = HUGO_DEFAULT_BG;
	wc->bg = c;
}


/* CHARACTER AND TEXT MEASUREMENT

	For non-proportional printing, screen dimensions will be given
	in characters, not pixels.

	For proportional printing, screen dimensions need to be in
	pixels, and each width routine must take into account the
	current font and style.

	The hugo_strlen() function is used to give the length of
	the string not including any non-printing control characters.
*/

int hugo_charwidth(char a)
{
	/* As given here, this function works only for non-proportional
	   printing.  For proportional printing, hugo_charwidth() should
	   return the width of the supplied character in the current
	   font and style.
	*/

	if (a==FORCED_SPACE)
		return CHARWIDTH;         /* same as ' ' */

	else if ((unsigned char)a >= ' ') /* alphanumeric characters */

		return CHARWIDTH;         /* for non-proportional */

	return 0;
}

int hugo_textwidth(char *a)
{
	int i, slen, len = 0;

	slen = (int)strlen(a);

	for (i=0; i<slen; i++)
	{
		if (a[i]==COLOR_CHANGE) i+=2;
		else if (a[i]==FONT_CHANGE) i++;
		else
			len += hugo_charwidth(a[i]);
	}

	return len;
}

int hugo_strlen(char *a)
{
	int i, slen, len = 0;

	slen = (int)strlen(a);

	for (i=0; i<slen; i++)
	{
		if (a[i]==COLOR_CHANGE) i+=2;
		else if (a[i]==FONT_CHANGE) i++;
		else len++;
	}

	return len;
}


/*
 * Replacements for things the Glk port doesn't support:
 *
 */

#if !defined (SETTITLE_SUPPORTED)
void hugo_setgametitle(char *t)
{}
#endif

#if !defined (COMPILE_V25)
int hugo_hasvideo(void)
{
	return false;
}

int hugo_playvideo(HUGO_FILE infile, long reslength,
	char loop_flag, char background, int volume)
{
	fclose(infile);
	return true;
}

void hugo_stopvideo(void)
{}
#endif

#if !defined (GRAPHICS_SUPPORTED)
int hugo_hasgraphics(void)
{
/* Returns true if the current display is capable of graphics display */
	
/* If images are being diverted to a window outside of the Glk frame:
	return 2;
*/
	return false;	/* graphics unavailable */
}

int hugo_displaypicture(HUGO_FILE infile, long reslength)
{
	fclose(infile);
	return true;
}
#endif

#if !defined (SOUND_SUPPORTED)
int hugo_playmusic(HUGO_FILE infile, long reslength, char loop_flag)
{
	fclose(infile);
	return true;	/* not an error */
}

void hugo_musicvolume(int vol)
{}

void hugo_stopmusic(void)
{}

int hugo_playsample(HUGO_FILE infile, long reslength, char loop_flag)
{
	fclose(infile);
	return true;	/* not an error */
}

void hugo_samplevolume(int vol)
{}

void hugo_stopsample(void)
{}
#endif
