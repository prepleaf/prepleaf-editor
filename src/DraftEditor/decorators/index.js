import Draft from 'draft-js';
import inlineEquationDecorator from './inline-equation';
import inlineHighlightedTextDecorator from './inline-highlighted-text';

const { CompositeDecorator } = Draft;

const compositeDecorator = new CompositeDecorator([
	inlineEquationDecorator,
	inlineHighlightedTextDecorator,
]);
export default compositeDecorator;
