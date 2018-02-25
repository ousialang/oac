#define FORWARD_FLASH '/'
#define COLON ':'

string path_ellipsis(std::string path, int16_t* scores, uint16_t current_length, uint16_t desired_length) {
  if (!scores) { return path; }
}

string path_ellipsis_in_place(std::string path, uint16_t* scores, uint16_t current_length, uint16_t desired_length) {
  if (!scores) { return path; }
}

// Shorten a long filename.
//
// 1. We calculate a score for each character in the path string. The greater
//    the score for a particular character, the higher the chance it will be
//    erased.
// 3. We now need to erase n characters or more.
//    while maximizing the scores.
//      s r c / m o d e l s / c a r t / c a r t
//      0 1 2 2 2 3 4 5 6 7 2 1 2 3 4 2 0 1 2 3
//      src/mod…/cart.oa:240:19
//      s…/c….oa:240:19
// 4. Our goal is to maximize (score / erased characters)
uint16_t* path_scores(std::string path, uint16_t desired_length) {
	uint16_t length = strlen(path);
	if (desired_length >= length) { return NULL; }
	uint16_t scores[length];
	// We parse the URL bouncing back and forth from the end of the string to
	// the beginning: this is because central directories
	path_parsing_stage pps = ROOT_DIR;
	uint16_t i_left = 0;
	uint16_t i_right = length-1;
	// Parsing information
	uint16_t first_slash_i;
	uint16_t last_slash_i;
	uint16_t dir_i = 0;
	uint16_t base_score_of_current_dir = 0;
	// Root dir
	for (; i_left<length; i_left++) {
		if (path[i_left] == FORWARD_SLASH) {
			scores[i_left] = 1;
			first_slash_i = i_left;
			break;
		} else {
			scores[i_left] = 1;
		}
	}
	// Column and line number
	for (;; i_right--) {
		scores[i_right] = 3;
		if (path[i_right] == COLON) {
			break;
		}
	}
	for (;; i_right--) {
		scores[i_right] = 2;
		if (path[i_right] == COLON) {
			break;
		}
	}
	// File extension
	for (;; i_right--) {
		scores[i] = 1;
		if (path[i] == '.') {
			break;
		}
	}
	// Filename
	uint16_t end_of_filename_i = i_right;
	for (;; i_right--) {
		if (path[i_right] == FORWARD_SLASH) {
			for (; end_of_filename_i>i_right; i_right--) {
				path[i_right] = end_of_filename_i - i_right;
			}
			break;
		}
	}
	left_side:
		if (i_left >= i_right) { goto return; }
		if (path[i_left] == FORWARD_SLASH) {
			scores[i_left] = 2;
		} else if (path[i_left-1] == FORWARD_SLASH) {
			base_score_of_current_dir++;
			scores[i_left] = base_score_of_current_dir + dir_i++;
		} else {
		  scores[i_left];
		}
		goto left_side;
	//right_side:
	return:
		return path;
}
