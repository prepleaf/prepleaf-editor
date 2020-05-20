import { CompositeDecorator } from 'draft-js';
import inlineEquationDecorator from './inline-equation';
const compositeDecorator = new CompositeDecorator([inlineEquationDecorator]);
export default compositeDecorator;
