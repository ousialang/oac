#ifndef TREE_H_
#define TREE_H_

#include <stdbool.h>
#include <stdlib.h>

#ifndef TREE_TYPE
#define TREE_TYPE int
#endif

typedef struct tree {
	TREE_TYPE info;
	struct tree* parent;
	struct tree* lchild;
	struct tree* rsibling;
} tree;

tree* tree_init(TREE_TYPE x);

tree* tree_common_ancestor(tree* t0, tree* t1);
tree** tree_children(tree* t);
tree** tree_siblings(tree* t);
tree** tree_pedigree(tree* t);

bool tree_is_root(tree* t);
bool tree_is_leaf(tree* t);
bool tree_is_inode(tree* t);
bool tree_are_siblings(tree* t0, tree* t1);
bool tree_is_older_sibling(tree* older, tree* younger);

void tree_swap(tree* t0, tree* t1);
void tree_kill(tree* t);

size_t tree_depth(tree* inode);
size_t tree_level(tree* t);
size_t tree_height(tree* root);
size_t tree_degree(tree* t);
size_t tree_count_siblings(tree* t);
size_t tree_count_children(tree* t);

#endif
