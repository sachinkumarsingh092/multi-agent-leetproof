"""RAG system for retrieving similar specifications using Embedding + BM25."""

import json
import numpy as np
from pathlib import Path
from typing import List, Dict, Tuple
from rank_bm25 import BM25Okapi
from logging_config import get_logger
from utils.lean_explore_service import search_lean as lean_search_service
from utils.message_helpers import lean_block

logger = get_logger(__name__)


class SpecRAG:
    """Hybrid retrieval system using BGE Embedding + BM25 for specification examples.

    Default embedding model: BAAI/bge-base-en-v1.5 (can be customized)
    Integrates with LeanExplore global service for searching Lean 4 declarations.
    """

    def __init__(
        self,
        knowledge_base_path: str | None = None,
        embedding_model: str = "BAAI/bge-base-en-v1.5",
        use_embeddings: bool = True
    ):
        """Initialize the RAG system.

        Args:
            knowledge_base_path: Path to the JSON knowledge base file
            embedding_model: Embedding model to use (default: BAAI/bge-base-en-v1.5)
            use_embeddings: Whether to use embeddings (default: True). Set to False for BM25-only mode.

        Note:
            LeanExplore integration is now always available via the global service.
            Use DISABLE_LEAN_EXPLORE environment variable to disable it.
        """
        if knowledge_base_path is None:
            import os
            base = Path(os.environ.get('LLOOM_BASE_DIR', Path(__file__).parent.parent))
            kb_path: Path = base / "mbpp_rag_data.json"
        else:
            kb_path = Path(knowledge_base_path)

        self.knowledge_base_path = kb_path
        self.embedding_model = embedding_model
        self.use_embeddings = use_embeddings
        self.specs = []
        self.bm25 = None
        self.embeddings_cache = {}
        self._bge_model = None  # Lazy load BGE embedding model

        if not use_embeddings:
            logger.info("Embeddings disabled - using BM25-only mode")

        self._load_knowledge_base()
        self._initialize_bm25()

    def _load_knowledge_base(self):
        """Load the specification knowledge base from JSON."""
        logger.info(f"Loading knowledge base from {self.knowledge_base_path}")

        with open(self.knowledge_base_path, 'r') as f:
            self.specs = json.load(f)

        logger.info(f"Loaded {len(self.specs)} specifications")

    def _initialize_bm25(self):
        """Initialize BM25 index with tokenized documents."""
        logger.info("Initializing BM25 index")

        # Tokenize each document (problem_description + spec_code)
        tokenized_corpus = []
        for spec in self.specs:
            # Combine problem description and spec code for better matching
            text = spec["problem_description"] + " " + spec["spec_code"]
            # Simple tokenization: lowercase and split by whitespace
            tokens = text.lower().split()
            tokenized_corpus.append(tokens)

        self.bm25 = BM25Okapi(tokenized_corpus)
        logger.info("BM25 index initialized")

    def _load_bge_model(self):
        """Lazy load BGE embedding model using SentenceTransformer.

        Returns:
            SentenceTransformer model instance or None if loading fails
        """
        # Check if embeddings are disabled
        if not self.use_embeddings:
            logger.debug("Embeddings disabled, skipping model load")
            return None

        if self._bge_model is not None:
            return self._bge_model

        try:
            from sentence_transformers import SentenceTransformer
            import torch

            logger.info(f"Loading BGE embedding model: {self.embedding_model}")

            # Check if CUDA is available
            device = "cuda" if torch.cuda.is_available() else "cpu"
            logger.info(f"Using device: {device}")

            logger.info("Initializing model (this may take 10-30 seconds)...")
            logger.warning("It spends ~500MB memory. It may be interrupted by OS if you don't have enough memory")
            self._bge_model = SentenceTransformer(
                self.embedding_model,
                device=device
            )
            logger.info(f"✓ BGE embedding model ({self.embedding_model}) loaded successfully")
            return self._bge_model

        except ImportError:
            logger.warning("sentence-transformers not installed. Install with: pip install -U sentence-transformers")
            return None
        except MemoryError as e:
            logger.error("=" * 80)
            logger.error("❌ MEMORY ERROR: Not enough RAM to load BGE embedding model")
            logger.error("=" * 80)
            logger.error(f"Error details: {e}")
            logger.error("")
            logger.error("Solutions:")
            logger.error("  1. Close other memory-intensive applications")
            logger.error("  2. Disable embeddings: set DISABLE_RAG_EMBEDDINGS=1")
            logger.error("  3. Use BM25-only mode: SpecRAG(use_embeddings=False)")
            logger.error(f"  4. Increase system RAM ({self.embedding_model} requires ~500MB-1GB)")
            logger.error("=" * 80)
            return None
        except RuntimeError as e:
            # Check for CUDA out of memory
            if "out of memory" in str(e).lower() or "cuda" in str(e).lower():
                logger.error("=" * 80)
                logger.error("❌ GPU MEMORY ERROR: Not enough VRAM to load model on GPU")
                logger.error("=" * 80)
                logger.error(f"Error details: {e}")
                logger.error("")
                logger.error("Attempting to fall back to CPU...")
                logger.error("=" * 80)
                # Try loading on CPU as fallback
                try:
                    from sentence_transformers import SentenceTransformer as ST
                    logger.info("Retrying with CPU device...")
                    self._bge_model = ST(
                        self.embedding_model,
                        device="cpu"
                    )
                    logger.info(f"✓ BGE embedding model ({self.embedding_model}) loaded successfully on CPU")
                    return self._bge_model
                except Exception as cpu_error:
                    logger.error(f"Failed to load on CPU as well: {cpu_error}")
                    logger.error("Solutions:")
                    logger.error("  1. Free up system memory")
                    logger.error("  2. Disable embeddings: set DISABLE_RAG_EMBEDDINGS=1")
                    logger.error("  3. Use BM25-only mode: SpecRAG(use_embeddings=False)")
                    return None
            else:
                logger.error(f"Failed to load BGE embedding model: {e}", exc_info=True)
                return None
        except OSError as e:
            # Check for memory allocation errors
            if "cannot allocate memory" in str(e).lower() or "errno 12" in str(e).lower():
                logger.error("=" * 80)
                logger.error("❌ MEMORY ALLOCATION ERROR: System cannot allocate memory")
                logger.error("=" * 80)
                logger.error(f"Error details: {e}")
                logger.error("")
                logger.error("Solutions:")
                logger.error("  1. Free up system memory (close applications)")
                logger.error("  2. Disable embeddings: set DISABLE_RAG_EMBEDDINGS=1")
                logger.error("  3. Use BM25-only mode: SpecRAG(use_embeddings=False)")
                logger.error("  4. Increase swap space or system RAM")
                logger.error("=" * 80)
                return None
            else:
                logger.error(f"Failed to load BGE embedding model: {e}", exc_info=True)
                return None
        except Exception as e:
            logger.error(f"Failed to load BGE embedding model: {e}", exc_info=True)
            return None

    def _get_embedding(self, text: str) -> np.ndarray | None:
        """Get embedding for a text using SentenceTransformer.

        Args:
            text: Text to embed

        Returns:
            Embedding vector as numpy array, or None if embedding fails
        """
        # Check cache first
        if text in self.embeddings_cache:
            return self.embeddings_cache[text]

        try:
            # Load model if not already loaded
            model = self._load_bge_model()
            if model is None:
                logger.debug("Model not available, skipping embedding")
                self.embeddings_cache[text] = None
                return None

            # Generate embedding using SentenceTransformer
            # The encode method returns numpy array directly
            embedding = model.encode(text, convert_to_numpy=True)

            # Cache the embedding
            embedding_array = np.array(embedding)
            self.embeddings_cache[text] = embedding_array
            return embedding_array

        except Exception as e:
            logger.debug(f"Error getting embedding: {e}")
            # Cache None to avoid repeated attempts
            self.embeddings_cache[text] = None
            return None

    def _get_spec_embeddings(self) -> List[np.ndarray] | None:
        """Get embeddings for all specs in knowledge base.

        Returns:
            List of embedding vectors, or None if embeddings unavailable
        """
        try:
            # Load model if not already loaded
            model = self._load_bge_model()
            if model is None:
                logger.debug("Model not available for batch embedding")
                return None

            # Collect texts for batch processing
            texts = []
            for spec in self.specs:
                # Combine problem description and spec code for better matching
                text = spec["problem_description"] + " " + spec["spec_code"]
                # Check if already cached
                if text in self.embeddings_cache:
                    continue
                texts.append(text)

            # Generate embeddings in batch if there are uncached texts
            if texts:
                logger.info(f"Generating embeddings for {len(texts)} specifications (batch mode)")
                logger.info("This may take 10-60 seconds depending on your hardware...")

                try:
                    # SentenceTransformer encode returns numpy array directly
                    batch_embeddings = model.encode(
                        texts,
                        batch_size=12,
                        convert_to_numpy=True,
                        show_progress_bar=True
                    )
                    logger.info(f"✓ Generated {len(batch_embeddings)} embeddings")

                    # Cache the embeddings
                    for text, embedding in zip(texts, batch_embeddings):
                        self.embeddings_cache[text] = np.array(embedding)

                    logger.info(f"✓ Cached {len(texts)} embeddings")
                except Exception as e:
                    logger.error(f"Error during batch embedding: {e}", exc_info=True)
                    return None

            # Collect all embeddings in order
            embeddings = []
            for spec in self.specs:
                # Combine problem description and spec code for consistency
                text = spec["problem_description"] + " " + spec["spec_code"]
                embedding = self.embeddings_cache.get(text)
                if embedding is None:
                    return None  # If any embedding is missing, return None
                embeddings.append(embedding)

            return embeddings

        except Exception as e:
            logger.warning(f"Error generating batch embeddings: {e}")
            return None

    def _cosine_similarity(self, vec1: np.ndarray, vec2: np.ndarray) -> float:
        """Calculate cosine similarity between two vectors.

        Args:
            vec1: First vector
            vec2: Second vector

        Returns:
            Cosine similarity score (0-1)
        """
        dot_product = np.dot(vec1, vec2)
        norm1 = np.linalg.norm(vec1)
        norm2 = np.linalg.norm(vec2)

        if norm1 == 0 or norm2 == 0:
            return 0.0

        return dot_product / (norm1 * norm2)

    def _bm25_search(self, query: str, top_k: int = 10) -> List[Tuple[int, float]]:
        """Search using BM25.

        Args:
            query: Query text
            top_k: Number of top results to return

        Returns:
            List of (index, score) tuples
        """
        if self.bm25 is None:
            logger.warning("BM25 not initialized, returning empty results")
            return []

        tokenized_query = query.lower().split()
        scores = self.bm25.get_scores(tokenized_query)

        # Get top k indices
        top_indices = np.argsort(scores)[::-1][:top_k]
        results = [(int(idx), float(scores[idx])) for idx in top_indices]

        return results

    def _embedding_search(self, query: str, top_k: int = 10) -> List[Tuple[int, float]] | None:
        """Search using embedding similarity.

        Args:
            query: Query text
            top_k: Number of top results to return

        Returns:
            List of (index, score) tuples, or None if embeddings unavailable
        """
        query_embedding = self._get_embedding(query)
        if query_embedding is None:
            return None

        spec_embeddings = self._get_spec_embeddings()
        if spec_embeddings is None:
            return None

        # Calculate cosine similarity with each spec
        similarities = []
        for idx, spec_embedding in enumerate(spec_embeddings):
            similarity = self._cosine_similarity(query_embedding, spec_embedding)
            similarities.append((idx, similarity))

        # Sort by similarity and get top k
        similarities.sort(key=lambda x: x[1], reverse=True)
        return similarities[:top_k]

    def _reciprocal_rank_fusion(
        self,
        bm25_results: List[Tuple[int, float]],
        embedding_results: List[Tuple[int, float]],
        k: int = 60
    ) -> List[Tuple[int, float]]:
        """Combine BM25 and embedding results using Reciprocal Rank Fusion.

        RRF formula: score(d) = sum_r( 1 / (k + rank_r(d)) )
        where r iterates over all ranking functions

        Args:
            bm25_results: BM25 search results
            embedding_results: Embedding search results
            k: RRF constant (default 60)

        Returns:
            Combined and re-ranked results
        """
        rrf_scores = {}

        # Add BM25 ranks
        for rank, (idx, _) in enumerate(bm25_results, start=1):
            if idx not in rrf_scores:
                rrf_scores[idx] = 0
            rrf_scores[idx] += 1 / (k + rank)

        # Add embedding ranks
        for rank, (idx, _) in enumerate(embedding_results, start=1):
            if idx not in rrf_scores:
                rrf_scores[idx] = 0
            rrf_scores[idx] += 1 / (k + rank)

        # Sort by RRF score
        sorted_results = sorted(rrf_scores.items(), key=lambda x: x[1], reverse=True)
        return sorted_results

    def retrieve(
        self,
        query: str,
        top_k: int = 3,
        bm25_weight: float = 0.5,
        embedding_weight: float = 0.5
    ) -> List[Dict]:
        """Retrieve top-k similar specifications using hybrid search.

        Args:
            query: Query problem description
            top_k: Number of results to return
            bm25_weight: Weight for BM25 scores (0-1) [currently unused, for future weighted combination]
            embedding_weight: Weight for embedding scores (0-1) [currently unused, for future weighted combination]

        Returns:
            List of specification dictionaries with similarity scores
        """
        logger.info(f"Retrieving top-{top_k} similar specifications for query")

        # Perform BM25 search
        bm25_results = self._bm25_search(query, top_k=top_k * 2)
        if bm25_results:
            logger.debug(f"BM25 top result: idx={bm25_results[0][0]}, score={bm25_results[0][1]:.4f}")

        # Perform embedding search
        embedding_results = self._embedding_search(query, top_k=top_k * 2)
        if embedding_results:
            logger.debug(f"Embedding top result: idx={embedding_results[0][0]}, score={embedding_results[0][1]:.4f}")
        else:
            logger.info("Embedding search unavailable, using BM25-only retrieval")

        # Combine results
        if embedding_results and bm25_results:
            # Use RRF when both are available
            combined_results = self._reciprocal_rank_fusion(bm25_results, embedding_results)
        elif bm25_results:
            # Fall back to BM25 only
            combined_results = bm25_results
        else:
            # No results available
            logger.warning("No retrieval results available")
            return []

        # Get top k results
        top_results = []
        for idx, score in combined_results[:top_k]:
            spec = self.specs[idx].copy()
            spec["rag_score"] = score
            top_results.append(spec)

        logger.info(f"Retrieved {len(top_results)} specifications")
        return top_results

    def format_examples_for_prompt(self, examples: List[Dict]) -> str:
        """Format retrieved examples for inclusion in prompt.

        Args:
            examples: List of specification examples

        Returns:
            Formatted string for prompt
        """
        if not examples:
            return ""

        formatted = "# Similar Specification Examples\n\n"
        formatted += "Below are some similar specification examples that may help guide your implementation:\n\n"

        for i, example in enumerate(examples, 1):
            formatted += f"## Example {i}\n\n"

            # Clean up problem description to remove redundant prefixes
            problem_desc = example['problem_description']
            # Remove common prefixes to avoid duplication
            prefixes_to_remove = [
                "Problem Description: ",
                "MBPP Problem ",
                "Problem: "
            ]
            for prefix in prefixes_to_remove:
                if problem_desc.startswith(prefix):
                    # For "MBPP Problem N:", keep the number
                    if prefix == "MBPP Problem " and ": " in problem_desc:
                        # Extract number and description
                        parts = problem_desc.split(": ", 1)
                        if len(parts) == 2:
                            problem_desc = parts[1]
                    else:
                        problem_desc = problem_desc[len(prefix):]
                    break

            formatted += f"**Problem:** {problem_desc}\n\n"
            formatted += f"**Specification:**\n{lean_block(example['spec_code'])}\n\n"
            formatted += "---\n\n"

        return formatted

    async def search_lean(
        self,
        query: str,
        top_k: int = 5,
        package_filters: List[str] | None = None
    ) -> List[Dict]:
        """Search Lean 4 declarations using LeanExplore.

        Args:
            query: Search query for Lean declarations
            top_k: Number of results to return (after filtering abbrev)
            package_filters: Optional list of package names to filter results

        Returns:
            List of Lean declaration dictionaries with metadata (abbrev filtered out)

        Note:
            This method uses the global LeanExplore service. Control via DISABLE_LEAN_EXPLORE env var.
        """
        logger.info(f"Searching Lean declarations for: {query}")

        try:
            # Use the global lean_search_service which handles abbrev filtering
            results = await lean_search_service(
                query=query,
                limit=top_k,
                filter_abbrev=True,
                package_filters=package_filters
            )

            logger.info(f"Found {len(results)} Lean declarations")
            return results

        except Exception as e:
            logger.error(f"Error searching Lean declarations: {e}", exc_info=True)
            return []

    def format_lean_results_for_prompt(self, results: List[Dict]) -> str:
        """Format Lean search results for inclusion in prompt.

        Args:
            results: List of Lean declaration results from search_lean()

        Returns:
            Formatted string for prompt
        """
        if not results:
            return ""

        formatted = "# Relevant Lean 4 Declarations\n\n"
        formatted += "Below are relevant Lean 4 declarations that may be useful:\n\n"

        for i, result in enumerate(results, 1):
            formatted += f"## Declaration {i}\n\n"

            # Lean name
            if result.get('lean_name'):
                formatted += f"**Name:** `{result['lean_name']}`\n\n"

            # Informal description
            if result.get('informal_description'):
                desc = result['informal_description']
                formatted += f"**Description:** {desc}\n\n"

            # Docstring
            if result.get('docstring'):
                docstring = result['docstring']
                formatted += f"**Documentation:**\n{docstring}\n\n"

            # Formal statement
            if result.get('statement_text'):
                stmt = result['statement_text']
                formatted += f"**Formal Statement:**\n{lean_block(stmt)}\n\n"

            # Source location
            if result.get('source_file'):
                formatted += f"**Source:** `{result['source_file']}`\n\n"

            formatted += "---\n\n"

        return formatted

# Global instance for reuse
_rag_instance = None


def get_rag_instance(
    use_embeddings: bool | None = None
) -> SpecRAG:
    """Get or create the global RAG instance.

    Args:
        use_embeddings: Whether to use embeddings. If None, reads from env var
                       DISABLE_RAG_EMBEDDINGS (set to "1" or "true" to disable)

    Returns:
        SpecRAG instance

    Note:
        The global instance is created on first call. Subsequent calls with different
        parameters will return the existing instance (parameters are ignored).
        To change parameters, create a new SpecRAG instance directly.
        LeanExplore integration is always available via the global service.
        Use DISABLE_LEAN_EXPLORE environment variable to disable it.
    """
    global _rag_instance
    if _rag_instance is None:
        # Check environment variable if not specified
        if use_embeddings is None:
            import os
            disable_env = os.getenv("DISABLE_RAG_EMBEDDINGS", "").lower()
            use_embeddings = disable_env not in ("1", "true", "yes")

        _rag_instance = SpecRAG(use_embeddings=use_embeddings)
    return _rag_instance
