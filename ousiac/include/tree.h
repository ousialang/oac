#ifndef TREE_H
#define TREE_H

#include <stdlib.h>

struct tree {
	int info;
	struct tree* parent;
	struct tree* lchild;
	struct tree* rsibling;
};

struct tree* tree_common_ancestor(struct tree* t0, struct tree* t1);
struct tree** tree_children(struct tree* t);
struct tree** tree_siblings(struct tree* t);
struct tree** tree_pedigree(struct tree* t);

bool tree_is_root(struct tree* t);
bool tree_is_leaf(struct tree* t);
bool tree_is_inode(struct tree* t);
bool tree_has_children(struct tree* t);
bool tree_has_siblings(struct tree* t);
bool tree_are_siblings(struct tree* t0, struct tree* t1);
bool tree_is_older_sibling(struct tree* older, struct tree* younger);

void tree_swap(struct tree* t0, struct tree* t1);
void tree_kill(struct tree* t);

size_t tree_depth(struct tree* inode);
size_t tree_level(struct tree* t);
size_t tree_height(struct tree* root);
size_t tree_degree(struct tree* t);
size_t tree_num_siblings(struct tree* t);

#endif
