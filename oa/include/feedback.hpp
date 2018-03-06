#ifndef FEEDBACK_H_
	#define FEEDBACK_H_

	typedef struct feedback feedback;

	feedback* feedback_init(void);
	void feedback_write_heading_with_formula(char* formula, feedback* fb);
	void feedback_write_heading(feedback* fb);

	void feedback_write_error(feedback* fb);
	void feedback_write_warning(feedback* fb);
	void feedback_write_note(feedback* fb);

	void feedback_write(char str[], feedback* fb);
	void feedback_write_wrap(feedback* fb);
	void feedback_write_wrap_text(char* text, feedback* fb);
	void feedback_write_line_right_align(char* str, feedback* fb);

	void feedback_printk(feedback* fb);
#endif
