#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include "utils/tree.h"

// #define NDEBUG
#include <assert.h>

#define max(x, y) (((x) > (y)) ? (x) : (y))

tree* tree_init(TREE_TYPE x) {
	tree* t = malloc(sizeof(tree));
	if (!t) {
		return NULL;
	}
	t->info = x;
	t->parent = NULL;
	t->lchild = NULL;
	t->rsibling = NULL;
	return t;
}

// HELPERS
// =======

tree* tree_container_helper(tree* t0, tree* t1) {
	if (t0 == t1 || !t0) {
		return t0;
	}
	return tree_container_helper(t1, t0->parent);
}

bool tree_is_leaf(tree* t) {
	return !(t->lchild);
}

bool tree_is_root(tree* t) {
	return !(t->parent);
}

size_t tree_count_children(tree* t) {
	size_t n = 0;
	t = t->lchild;
	while (t) {
		n++;
		t = t->rsibling;
	}
	return n;
}

size_t tree_count_siblings(tree* t) {
	size_t n = 0;
	t = t->rsibling;
	while(t) {
		n++;
		t = t->rsibling;
	}
	return n;
}

tree** tree_siblings(tree* t) {
	size_t n = tree_count_siblings(t);
	tree** siblings = malloc(sizeof(tree*) * n);
	t = t->lchild;
	while (n > 0) {
		n--;
		siblings[n] = t->rsibling;
	}
	return siblings;
}

tree** tree_pedigree(tree* t) {
	size_t lvl = tree_level(t);
	tree** pedigree = malloc(sizeof(tree*) * lvl);
	while (lvl>0) {
		lvl--;
		pedigree[lvl] = t->parent;
	}
	return pedigree;
}

size_t tree_depth(tree* t) {
	size_t depth = -1;
	do {
		t = t->parent;
		depth++;
	} while (t);
	return depth;
}

size_t tree_level(tree* t) { return tree_depth(t+1); }

size_t tree_height(tree* t) {
	if (tree_is_leaf(t)) {
		return 0;
	} else if (tree_count_siblings(t) > 0) {
		return 1 + tree_height(t->lchild);
	} else {
		return max(tree_height(t->lchild), tree_height(t->rsibling));
	}
}

tree** tree_children(tree* t) {
	size_t n = tree_count_children(t);
	tree** children = malloc(sizeof(tree*) * n);
	t = t->lchild;
	while (n > 0) {
		n--;
		children[n] = t->rsibling;
	}
	return children;
}

void tree_swap(tree* t0, tree* t1) {
	tree* ttemp = t0;
	t0->parent = t1->parent;
	t1->parent = ttemp->parent;
	t0->rsibling = t1->rsibling;
	t1->rsibling = ttemp->rsibling;
}
/*
tree* tree_iter_prefix(tree* tree) {
    tree_iter_prefix(tree->lchild);
    if (tree->lchild == NULL) { return tree; }
}*/

int tree_kill_children(tree* tree) {
	tree_kill(tree->lchild);
	tree->lchild = NULL;
	return 0;
}

bool tree_are_siblings(tree* t0, tree* t1) {
	return tree_is_older_sibling(t0, t1) || tree_is_older_sibling(t1, t0);
}

bool tree_is_older_sibling(tree* older, tree* younger) {
	while (older) {
		if (older->rsibling == younger) {
			return true;
		}
		older = older->rsibling;
	}
	return false;
}

bool tree_is_ancestor(tree* ancestor, tree* descendant) {
	if (descendant->parent == ancestor) {
		return true;
	}
	return tree_is_ancestor(ancestor, descendant->parent);
}

void tree_kill(tree* t) {
	if (!t)
		return;
	tree_kill(t->lchild);
	tree_kill(t->rsibling);
	free(t);
}

size_t tree_size(tree* t) {
	if (tree_is_leaf(t)) {
		return 1;
	}
	return 1 + tree_size(t->lchild) + tree_size(t->rsibling);
}

tree* tree_container(tree* t0, tree* t1) {
	if (!t1) {
		return NULL;
	} // t0 is checked by tree_container_helper
	return tree_container_helper(t0, t1);
}

int tree_prepend_child(tree* t, TREE_TYPE info) {
	t->lchild = &(tree){
		.info = info,
		.parent = t,
		.lchild = NULL,
		.rsibling = t->lchild,
	};
	return 0;
}
