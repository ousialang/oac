#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <signal.h>
#include <sys/ioctl.h>
#include <unistd.h>
#include <ncurses.h>
#include "feedback/feedback.h"
#include "utils/ansi.h"

#define FEEDBACK_MAX_WRAP_WIDTH 79
#define FEEDBACK_MIN_WRAP_WIDTH 29
#define FEEDBACK_BATCH_SIZE 8
#define FORWARD_SLASH '/'

uint16_t feedback_terminal_size(void) {
	struct winsize w;
	ioctl(0, TIOCGSIZE, &w);
	return w.ws_col;
}

// NB: after calling feedback_init, you MUST call feedback_write_heading
// (with_formula or not).
feedback* feedback_init(void) {
	uint16_t wrap_width = feedback_terminal_size();
	// Normalize wrap_width into reasonable limits.
	if (wrap_width < FEEDBACK_MIN_WRAP_WIDTH) {
		wrap_width = FEEDBACK_MIN_WRAP_WIDTH;
	} else if (wrap_width > FEEDBACK_MAX_WRAP_WIDTH) {
		wrap_width = FEEDBACK_MAX_WRAP_WIDTH;
	}
	// We malloc at the same time for feedback, feedback_batch, and the first
	// line of the feedback message, which we will need for sure.
	feedback* fb = malloc(sizeof(feedback) + sizeof(feedback_batch)
						  // the first line (with newline)
						  + wrap_width + 2 * ANSI_LENGTH + 2);
	if (!fb) {
		return NULL;
	}
	fb->wrap_width = wrap_width;
	fb->current_width = wrap_width;
	fb->strs_n = 1;
	feedback_batch* fbb = (feedback_batch*)(fb + sizeof(feedback));
	fbb->next = NULL;
	fbb->str[0] = (char*)(fbb+sizeof(feedback_batch));
	fb->head_batch = fbb;
	fb->tail_batch = fbb;
	return fb;
}

void feedback_write_heading_with_formula(char* formula, feedback* fb) {
	sprintf(fb->tail_batch->str[0], "--- " ANSI_BOLD "%s" ANSI_RESET " %.*d\n", formula,
	        (int)(fb->wrap_width - 5 - strlen(formula)), '-');
}

void feedback_write_heading(feedback* fb) {
	sprintf(fb->tail_batch->str[0], "%.*d\n", (int)(fb->wrap_width), '-');
}

void feedback_write(char* str, feedback* fb) {
	if (fb->strs_n % FEEDBACK_BATCH_SIZE == 0) {
		feedback_batch* fbb = malloc(sizeof(feedback_batch));
		fb->tail_batch->next = fbb;
		fb->tail_batch = fbb;
	}
	fb->tail_batch->str[fb->strs_n++] = str;
	if (strcmp(str, "\n") == 0) {
		fb->current_width = 0;
	} else {
		fb->current_width += strlen(str);
	}
}

void feedback_write_ra(char* str, feedback* fb) {
	uint16_t str_n = strlen(str);
	uint16_t spaces_n = fb->wrap_width - str_n;
	char spaces[spaces_n];
	memset(spaces, ' ', spaces_n);
	spaces[spaces_n] = '\0';
	if (fb->current_width != 0) {
		feedback_write_nl(fb);
	}
	feedback_write(spaces, fb);
	feedback_write(str, fb);
}

void feedback_write_wrap(char* str, feedback* fb) {
	fb->tail_batch->str[fb->strs_n++] = str;
	uint16_t length = strlen(str);
	if (fb->current_width + length > fb->wrap_width) {
		feedback_write("\n", fb);
		fb->current_width = 0;
	}
	feedback_write(str, fb);
}

// Print and kill
void feedback_printk(feedback* fb) {
	feedback_batch* fbb = fb->head_batch;
	size_t i = 0;
	for (i=0; i<fb->strs_n; i++) {
		printf("%s", fbb->str[i]);
		if (fb->strs_n % FEEDBACK_BATCH_SIZE == 0) {
			fbb = fbb->next;
		}
	}
}

void feedback_write_nl(feedback* fb) {
	feedback_write("\n", fb);
}

void feedback_write_error(feedback* fb) {
	char str[] = ANSI_RED "ERROR:" ANSI_RESET;
	feedback_write_wrap(str, fb);
	fb->current_width -= 2 * ANSI_LENGTH;
}

void feedback_write_warning(feedback* fb) {
	char str[] = ANSI_YELLOW "WARNING:" ANSI_RESET;
	feedback_write_wrap(str, fb);
	fb->current_width -= 2 * ANSI_LENGTH;
}

void feedback_write_note(feedback* fb) {
	feedback_write_wrap("NOTE:", fb);
}

typedef enum {
	TOP_DIR,
	DIR,
	FILENAME
	LINE_NUM,
	COL_NUM,
} feedback_info;

char* feedback_ellipsis(char* str, uint16_t scores[], uint16_t desired_length) {
	uint16_t i = 0;
	uint16_t j = strlen(str) - desired_length;
	if (scores[j] >= scores[i]) {
		i++;
		j++;
	}
}

void feedback_write_text(char* text, feedback* fb) {
	uint16_t i;
	uint16_t i_last;
	uint32_t text_len = strlen(text);
	for (i = 0; i < text_len; i++, fb->current_width++) {
		if (text[i] == ' ') {
			i_last = i + 1;
		}
	}
	feedback_write_wrap(&text[i_last], fb);
}

void feedback_write_wrap_right_align(char* word, feedback* fb) {
	uint16_t spaces_num = fb->wrap_width - strlen(word);
	char spaces[spaces_num + 1];
	memset(spaces, ' ', spaces_num);
	feedback_write(spaces, fb);
	feedback_write(word, fb);
}
